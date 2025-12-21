// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translation from IRNode to Z3 AST

use crate::data::types::TempId;
use crate::data::Program;
use crate::{BinOp, BitOp, Const, FunctionID, IRNode, StructID, Type, UnOp};
use std::collections::{HashMap, HashSet};
use z3::ast::{Ast, Bool, Dynamic, BV};
use z3::{Config, Context, Sort};

/// Maximum number of loop iterations for bounded unrolling
const MAX_LOOP_UNROLL: usize = 4;

/// SMT context for translating IR to Z3
pub struct SmtContext<'ctx, 'prog> {
    pub ctx: &'ctx Context,
    /// Variable bindings (name -> Z3 AST)
    vars: HashMap<String, Dynamic<'ctx>>,
    /// Program for looking up function bodies
    program: Option<&'prog Program>,
    /// Functions currently being translated (to detect recursion)
    in_progress: HashSet<FunctionID>,
    /// Current loop unrolling depth
    loop_depth: usize,
    /// Reverse mapping from Z3 variable names to IR expressions
    /// This allows us to convert Z3 output back to IR
    pub var_to_ir: HashMap<String, IRNode>,
    /// Tracks which variables hold single-field struct types
    /// Maps variable name -> struct_id for unwrapping during Z3->IR conversion
    var_struct_types: HashMap<String, StructID>,
}

impl<'ctx, 'prog> SmtContext<'ctx, 'prog> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            vars: HashMap::new(),
            program: None,
            in_progress: HashSet::new(),
            loop_depth: 0,
            var_to_ir: HashMap::new(),
            var_struct_types: HashMap::new(),
        }
    }

    /// Create a new context with program for function inlining
    pub fn with_program(ctx: &'ctx Context, program: &'prog Program) -> Self {
        Self {
            ctx,
            vars: HashMap::new(),
            program: Some(program),
            in_progress: HashSet::new(),
            loop_depth: 0,
            var_to_ir: HashMap::new(),
            var_struct_types: HashMap::new(),
        }
    }

    /// Bind a variable to a Z3 expression
    pub fn bind_var(&mut self, name: String, value: Dynamic<'ctx>) {
        self.vars.insert(name, value);
    }

    /// Create a fresh bitvector variable for a given type
    pub fn fresh_bv(&self, name: &str, bits: u32) -> BV<'ctx> {
        BV::new_const(self.ctx, name, bits)
    }

    /// Create a fresh boolean variable
    pub fn fresh_bool(&self, name: &str) -> Bool<'ctx> {
        Bool::new_const(self.ctx, name)
    }

    /// Translate an IR type to Z3 sort
    pub fn type_to_sort(&self, ty: &Type) -> Sort<'ctx> {
        match ty {
            Type::Bool => Sort::bool(self.ctx),
            Type::UInt(bits) => Sort::bitvector(self.ctx, *bits),
            Type::Address => Sort::bitvector(self.ctx, 256), // Addresses as 256-bit BV
            _ => Sort::bitvector(self.ctx, 256), // Default fallback
        }
    }

    /// Translate an IRNode to a Z3 boolean expression.
    /// Returns None if the expression cannot be translated to a boolean.
    pub fn translate_to_bool(&mut self, node: &IRNode) -> Option<Bool<'ctx>> {
        let dyn_ast = self.translate(node)?;
        dyn_ast.as_bool()
    }

    /// Translate an IRNode to a Z3 AST.
    /// Returns None if the expression contains unsupported constructs.
    pub fn translate(&mut self, node: &IRNode) -> Option<Dynamic<'ctx>> {
        match node {
            IRNode::Const(c) => self.translate_const(c),

            IRNode::Var(name) => self.vars.get(name).cloned(),

            IRNode::BinOp { op, lhs, rhs } => {
                let l = self.translate(lhs)?;
                let r = self.translate(rhs)?;
                self.translate_binop(*op, l, r)
            }

            IRNode::UnOp { op, operand } => {
                let o = self.translate(operand)?;
                self.translate_unop(*op, o)
            }

            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let c = self.translate_to_bool(cond)?;
                let t = self.translate(then_branch)?;
                let e = self.translate(else_branch)?;
                // Ensure both branches have the same sort for ITE
                match (t.as_bv(), e.as_bv()) {
                    (Some(t_bv), Some(e_bv)) => {
                        let (t_bv, e_bv) = self.match_bv_sizes(t_bv, e_bv);
                        Some(c.ite(&t_bv.into(), &e_bv.into()))
                    }
                    (Some(_), None) | (None, Some(_)) => {
                        // Type mismatch - one is BV, one isn't
                        None
                    }
                    (None, None) => {
                        // Both are booleans (or something else)
                        if t.as_bool().is_some() && e.as_bool().is_some() {
                            Some(c.ite(&t, &e))
                        } else {
                            None
                        }
                    }
                }
            }

            IRNode::Let { pattern, value } => {
                // Check if the value is a Call that returns a single-field struct
                // If so, track the struct type for the let-bound variable
                if let IRNode::Call { function, .. } = &**value {
                    if let Some(program) = self.program {
                        let func = program.functions.get(function);
                        if let Type::Struct { struct_id, .. } = &func.signature.return_type {
                            let struct_def = program.structs.get(struct_id);
                            if struct_def.fields.len() == 1 && pattern.len() == 1 {
                                self.var_struct_types.insert(pattern[0].clone(), *struct_id);
                            }
                        }
                    }
                }

                match self.translate(value) {
                    Some(v) => {
                        // For single-variable let bindings, add to context
                        if pattern.len() == 1 {
                            self.bind_var(pattern[0].clone(), v.clone());
                            // Map the let-bound variable to the value expression
                            // But NOT for While loops - those have internal variables that shouldn't leak
                            // The While loop result is already tracked via the _loop_N mappings
                            if !matches!(**value, IRNode::While { .. }) {
                                self.var_to_ir.insert(pattern[0].clone(), (**value).clone());
                            }
                        } else {
                            // Multi-variable let (tuple destructuring) - bind all with same value
                            // This is a simplification, but works for most cases
                            for name in pattern {
                                self.bind_var(name.clone(), v.clone());
                                if !matches!(**value, IRNode::While { .. }) {
                                    self.var_to_ir.insert(name.clone(), (**value).clone());
                                }
                            }
                        }
                        Some(v)
                    }
                    None => {
                        // Value translation failed - bind fresh symbolic variables
                        // so that subsequent code can continue
                        for name in pattern {
                            // Create a fresh 256-bit BV as a default symbolic value
                            let fresh: Dynamic<'ctx> = BV::new_const(self.ctx, name.as_str(), 256).into();
                            self.bind_var(name.clone(), fresh);
                            // Still record the mapping even if translation failed
                            self.var_to_ir.insert(name.clone(), (**value).clone());
                        }
                        // Return None to indicate translation failed
                        None
                    }
                }
            }

            IRNode::Block { children } => {
                // Translate all children, return the last one's value
                let mut result = None;
                for child in children {
                    // Continue even if a child fails - it might just be a side-effect
                    // that we can skip (like a log statement)
                    let child_result = self.translate(child);
                    if child_result.is_some() {
                        result = child_result;
                    }
                }
                result
            }

            IRNode::Tuple(elems) => {
                if elems.is_empty() {
                    // Unit - return a dummy true value
                    Some(Bool::from_bool(self.ctx, true).into())
                } else if elems.len() == 1 {
                    self.translate(&elems[0])
                } else {
                    // Multi-element tuples - translate each and return the last
                    // (SMT doesn't have native tuple support, so we approximate)
                    let mut last = None;
                    for elem in elems {
                        last = self.translate(elem);
                    }
                    last
                }
            }

            // Function calls - inline if we have the program
            IRNode::Call { function, args, .. } => {
                self.translate_call(*function, args)
            }

            // Struct construction
            IRNode::Pack { struct_id, fields, .. } => {
                self.translate_pack(*struct_id, fields)
            }

            // Field access
            IRNode::Field { struct_id, field_index, base } => {
                self.translate_field(*struct_id, *field_index, base)
            }

            // While loop - use bounded unrolling or invariants
            IRNode::While { cond, body, vars, invariants } => {
                self.translate_while(cond, body, vars, invariants)
            }

            // Return - extract the return value(s)
            IRNode::Return(values) => {
                match values.len() {
                    0 => Some(Bool::from_bool(self.ctx, true).into()), // unit return
                    1 => self.translate(&values[0]),
                    _ => {
                        // Multiple return values - translate each
                        // For now, return the last one (most common pattern)
                        self.translate(values.last()?)
                    }
                }
            }

            // Bit-level operations
            IRNode::BitOp(bit_op) => self.translate_bitop(bit_op),

            // These don't produce boolean values we can reason about directly
            IRNode::Abort(_)
            | IRNode::Unpack { .. }
            | IRNode::UpdateField { .. }
            | IRNode::UpdateVec { .. }
            | IRNode::Requires(_)
            | IRNode::Ensures(_)
            | IRNode::WhileAborts { .. } => None,
        }
    }

    fn translate_const(&self, c: &Const) -> Option<Dynamic<'ctx>> {
        match c {
            Const::Bool(b) => Some(Bool::from_bool(self.ctx, *b).into()),
            Const::UInt { bits, value } => {
                // Z3 BV from u64 - for larger values we need string conversion
                let bits = *bits as u32;
                if bits <= 64 {
                    Some(BV::from_u64(self.ctx, value.as_u64(), bits).into())
                } else {
                    // For larger bitvectors, use string representation
                    let s = format!("{}", value);
                    BV::from_str(self.ctx, bits, &s).map(|bv| bv.into())
                }
            }
            Const::Address(addr) => {
                let s = format!("{}", addr);
                BV::from_str(self.ctx, 256, &s).map(|bv| bv.into())
            }
            Const::Vector { .. } => None, // Vectors not directly supported
        }
    }

    /// Ensure two bitvectors have the same size by zero-extending the smaller one
    fn match_bv_sizes(&self, a: BV<'ctx>, b: BV<'ctx>) -> (BV<'ctx>, BV<'ctx>) {
        let a_size = a.get_size();
        let b_size = b.get_size();
        if a_size < b_size {
            (a.zero_ext(b_size - a_size), b)
        } else if b_size < a_size {
            (a, b.zero_ext(a_size - b_size))
        } else {
            (a, b)
        }
    }

    fn translate_binop(
        &self,
        op: BinOp,
        lhs: Dynamic<'ctx>,
        rhs: Dynamic<'ctx>,
    ) -> Option<Dynamic<'ctx>> {
        match op {
            // Logical operations (Bool -> Bool)
            BinOp::And => {
                let l = lhs.as_bool()?;
                let r = rhs.as_bool()?;
                Some(Bool::and(self.ctx, &[&l, &r]).into())
            }
            BinOp::Or => {
                let l = lhs.as_bool()?;
                let r = rhs.as_bool()?;
                Some(Bool::or(self.ctx, &[&l, &r]).into())
            }

            // Comparison operations (BV -> Bool)
            BinOp::Eq => {
                // Handle both bool and bv comparisons
                if let (Some(l), Some(r)) = (lhs.as_bool(), rhs.as_bool()) {
                    Some(l._eq(&r).into())
                } else if let (Some(l), Some(r)) = (lhs.as_bv(), rhs.as_bv()) {
                    let (l, r) = self.match_bv_sizes(l, r);
                    Some(l._eq(&r).into())
                } else {
                    None
                }
            }
            BinOp::Neq => {
                if let (Some(l), Some(r)) = (lhs.as_bool(), rhs.as_bool()) {
                    Some(l._eq(&r).not().into())
                } else if let (Some(l), Some(r)) = (lhs.as_bv(), rhs.as_bv()) {
                    let (l, r) = self.match_bv_sizes(l, r);
                    Some(l._eq(&r).not().into())
                } else {
                    None
                }
            }
            BinOp::Lt => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvult(&r).into())
            }
            BinOp::Le => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvule(&r).into())
            }
            BinOp::Gt => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvugt(&r).into())
            }
            BinOp::Ge => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvuge(&r).into())
            }

            // Arithmetic operations (BV -> BV)
            BinOp::Add => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvadd(&r).into())
            }
            BinOp::Sub => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvsub(&r).into())
            }
            BinOp::Mul => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvmul(&r).into())
            }
            BinOp::Div => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvudiv(&r).into())
            }
            BinOp::Mod => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvurem(&r).into())
            }

            // Bitwise operations (BV -> BV)
            BinOp::BitAnd => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvand(&r).into())
            }
            BinOp::BitOr => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvor(&r).into())
            }
            BinOp::BitXor => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                let (l, r) = self.match_bv_sizes(l, r);
                Some(l.bvxor(&r).into())
            }
            BinOp::Shl => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                // For shift, extend shift amount to match operand size
                let r_extended = if r.get_size() < l.get_size() {
                    r.zero_ext(l.get_size() - r.get_size())
                } else if r.get_size() > l.get_size() {
                    r.extract(l.get_size() - 1, 0)
                } else {
                    r
                };
                Some(l.bvshl(&r_extended).into())
            }
            BinOp::Shr => {
                let l = lhs.as_bv()?;
                let r = rhs.as_bv()?;
                // For shift, extend shift amount to match operand size
                let r_extended = if r.get_size() < l.get_size() {
                    r.zero_ext(l.get_size() - r.get_size())
                } else if r.get_size() > l.get_size() {
                    r.extract(l.get_size() - 1, 0)
                } else {
                    r
                };
                Some(l.bvlshr(&r_extended).into())
            }
        }
    }

    fn translate_unop(&self, op: UnOp, operand: Dynamic<'ctx>) -> Option<Dynamic<'ctx>> {
        match op {
            UnOp::Not => {
                let b = operand.as_bool()?;
                Some(b.not().into())
            }
            UnOp::BitNot => {
                let bv = operand.as_bv()?;
                Some(bv.bvnot().into())
            }
            UnOp::Cast(bits) => {
                let bv = operand.as_bv()?;
                Some(self.resize_bv(&bv, bits).into())
            }
        }
    }

    /// Resize a bitvector to target bits (truncate or zero-extend)
    fn resize_bv(&self, bv: &BV<'ctx>, target_bits: u32) -> BV<'ctx> {
        let current = bv.get_size();
        if current == target_bits {
            bv.clone()
        } else if current > target_bits {
            bv.extract(target_bits - 1, 0)
        } else {
            bv.zero_ext(target_bits - current)
        }
    }

    /// Translate bit-level operations (extract, concat, extend)
    fn translate_bitop(&mut self, bit_op: &BitOp) -> Option<Dynamic<'ctx>> {
        match bit_op {
            BitOp::Extract { high, low, operand } => {
                let op = self.translate(operand)?.as_bv()?;
                Some(op.extract(*high, *low).into())
            }
            BitOp::Concat { high, low } => {
                let h = self.translate(high)?.as_bv()?;
                let l = self.translate(low)?.as_bv()?;
                Some(h.concat(&l).into())
            }
            BitOp::ZeroExtend { bits, operand } => {
                let op = self.translate(operand)?.as_bv()?;
                Some(op.zero_ext(*bits).into())
            }
            BitOp::SignExtend { bits, operand } => {
                let op = self.translate(operand)?.as_bv()?;
                Some(op.sign_ext(*bits).into())
            }
        }
    }

    /// Translate a function call by inlining the function body
    fn translate_call(
        &mut self,
        func_id: FunctionID,
        args: &[IRNode],
    ) -> Option<Dynamic<'ctx>> {
        let program = self.program?;

        // Check for recursion
        if self.in_progress.contains(&func_id) {
            log::debug!("Recursion detected for {:?}, cannot inline", func_id);
            return None;
        }

        // Get the function
        let func = program.functions.get(&func_id);

        // Translate arguments
        let arg_values: Vec<_> = args
            .iter()
            .map(|arg| self.translate(arg))
            .collect::<Option<Vec<_>>>()?;

        // Save current variable bindings (but NOT var_to_ir - we want those to accumulate)
        let saved_vars = self.vars.clone();

        // Bind parameters to argument values and update var_to_ir mappings
        for (i, (param, value)) in func.signature.parameters.iter().zip(arg_values).enumerate() {
            self.vars.insert(param.name.clone(), value);

            // Map callee's parameter to the caller's argument expression
            // e.g., if calling f(x) where f has param "p", map "p" -> args[i]
            self.var_to_ir.insert(param.name.clone(), args[i].clone());

            // For struct parameters, also map the field accessor
            // e.g., if param is "num1: I32", map "num1_bits" -> Field(args[i], "bits")
            if let Type::Struct { struct_id, .. } = &param.param_type {
                let struct_def = program.structs.get(struct_id);
                if struct_def.fields.len() == 1 {
                    // Track that this variable holds a single-field struct
                    self.var_struct_types.insert(param.name.clone(), *struct_id);

                    let field = &struct_def.fields[0];
                    let field_var_name = format!("{}_{}", param.name, field.name);
                    let field_ir = IRNode::Field {
                        struct_id: *struct_id,
                        field_index: 0,
                        base: Box::new(args[i].clone()),
                    };
                    self.var_to_ir.insert(field_var_name, field_ir);
                }
            }
        }

        // Mark function as in progress
        self.in_progress.insert(func_id);

        // Translate the function body
        let result = self.translate(&func.body);

        // Restore variable bindings but keep var_to_ir mappings
        // (they need to persist for Z3 -> IR conversion later)
        self.in_progress.remove(&func_id);
        self.vars = saved_vars;

        result
    }

    /// Translate struct construction (Pack)
    /// For single-field structs (wrapper types), just return the field value.
    fn translate_pack(
        &mut self,
        _struct_id: StructID,
        fields: &[IRNode],
    ) -> Option<Dynamic<'ctx>> {
        // For single-field structs, just use the field value directly
        // This works well for wrapper types like I128 { bits: u128 }
        if fields.len() == 1 {
            return self.translate(&fields[0]);
        }
        // Multi-field structs not supported yet
        None
    }

    /// Translate field access
    /// For single-field structs, just return the struct value (which IS the field).
    fn translate_field(
        &mut self,
        struct_id: StructID,
        field_index: usize,
        base: &IRNode,
    ) -> Option<Dynamic<'ctx>> {
        let program = self.program?;
        let struct_def = program.structs.get(&struct_id);

        // For single-field structs, the base IS the field value
        if struct_def.fields.len() == 1 && field_index == 0 {
            return self.translate(base);
        }
        // Multi-field structs not supported yet
        None
    }

    /// Translate a while loop by introducing fresh symbolic variables.
    ///
    /// Since loops are difficult to unroll efficiently, we instead:
    /// 1. Update the loop variables to fresh symbolic values
    /// 2. Return the fresh symbolic result
    ///
    /// This is sound for proving "never aborts" because if we can prove
    /// the abort condition is unsatisfiable even with symbolic loop results,
    /// then it's definitely unsatisfiable.
    fn translate_while(
        &mut self,
        _cond: &IRNode,
        _body: &IRNode,
        vars: &[TempId],
        _invariants: &[IRNode],
    ) -> Option<Dynamic<'ctx>> {
        // Check for excessive loop nesting
        if self.loop_depth >= MAX_LOOP_UNROLL {
            return None;
        }

        self.loop_depth += 1;

        // For each loop variable, create a fresh symbolic value of the same type
        // We need to infer the type from the current binding
        let mut result_values = Vec::new();
        for (i, v) in vars.iter().enumerate() {
            let fresh_name = format!("{}_loop_{}", v, i);

            // Record mapping for loop result variable
            // If the variable is a single-field struct, map to field access
            // Otherwise, map to the variable directly
            if let Some(&struct_id) = self.var_struct_types.get(v) {
                // Variable holds a struct - map to field access for proper unwrapping
                let field_ir = IRNode::Field {
                    struct_id,
                    field_index: 0,
                    base: Box::new(IRNode::Var(v.clone())),
                };
                self.var_to_ir.insert(fresh_name.clone(), field_ir);
            } else {
                // Regular variable - map directly
                self.var_to_ir.insert(fresh_name.clone(), IRNode::Var(v.clone()));
            }

            // Get current value to infer type, or create a default bitvector
            if let Some(current) = self.vars.get(v) {
                // Create a fresh variable with the same type
                let fresh: Dynamic<'ctx> = if let Some(bv) = current.as_bv() {
                    BV::new_const(self.ctx, fresh_name.as_str(), bv.get_size()).into()
                } else if current.as_bool().is_some() {
                    Bool::new_const(self.ctx, fresh_name.as_str()).into()
                } else {
                    // Default to 256-bit BV
                    BV::new_const(self.ctx, fresh_name.as_str(), 256).into()
                };
                self.vars.insert(v.clone(), fresh.clone());
                result_values.push(fresh);
            } else {
                // Variable not found - this is likely a local variable defined in the loop
                // Create a fresh 32-bit BV as a reasonable default
                let fresh: Dynamic<'ctx> = BV::new_const(self.ctx, fresh_name.as_str(), 32).into();
                self.vars.insert(v.clone(), fresh.clone());
                result_values.push(fresh);
            }
        }

        self.loop_depth -= 1;

        // Return the tuple of fresh values
        self.make_tuple_value(&result_values)
    }

    /// Create a tuple value from multiple Dynamic values.
    /// For single values, just return the value directly.
    fn make_tuple_value(&self, values: &[Dynamic<'ctx>]) -> Option<Dynamic<'ctx>> {
        match values.len() {
            0 => Some(Bool::from_bool(self.ctx, true).into()),
            1 => Some(values[0].clone()),
            _ => {
                // For multi-value tuples, we need to handle this differently
                // For now, return the last value (common pattern in while loops)
                Some(values.last()?.clone())
            }
        }
    }

    /// Create a fresh struct variable with symbolic fields
    /// For single-field structs, just create the field value.
    /// Also records the mapping from Z3 name to IR expression.
    pub fn fresh_struct(&mut self, name: &str, struct_id: StructID) -> Option<Dynamic<'ctx>> {
        let program = self.program?;
        let struct_def = program.structs.get(&struct_id);

        // For single-field structs, just create the field
        if struct_def.fields.len() == 1 {
            let field = &struct_def.fields[0];
            let field_name = format!("{}_{}", name, field.name);

            // Record mapping: "num1_bits" -> Field { base: Var("num1"), field_index: 0 }
            let ir_expr = IRNode::Field {
                struct_id,
                field_index: 0,
                base: Box::new(IRNode::Var(name.to_string())),
            };
            self.var_to_ir.insert(field_name.clone(), ir_expr);

            return self.fresh_for_type(&field_name, &field.field_type);
        }
        // Multi-field structs not supported yet
        None
    }

    /// Create a fresh symbolic variable for any supported type
    pub fn fresh_for_type(&mut self, name: &str, ty: &Type) -> Option<Dynamic<'ctx>> {
        match ty {
            Type::Bool => Some(self.fresh_bool(name).into()),
            Type::UInt(bits) => Some(self.fresh_bv(name, *bits).into()),
            Type::SInt(bits) => Some(self.fresh_bv(name, *bits).into()),
            Type::Address => Some(self.fresh_bv(name, 256).into()),
            Type::Struct { struct_id, .. } => self.fresh_struct(name, *struct_id),
            _ => None,
        }
    }
}

/// Create a new Z3 config with reasonable defaults
pub fn default_config() -> Config {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(5000); // 5 second timeout
    cfg
}

/// Create a new Z3 context with default config
pub fn new_context() -> Context {
    Context::new(&default_config())
}
