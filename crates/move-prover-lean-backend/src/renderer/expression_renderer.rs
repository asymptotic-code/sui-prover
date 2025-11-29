// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Expression IR to Lean syntax.
//! Pure translation - pattern match IR nodes to Lean text.

use std::fmt::Write;
use intermediate_theorem_format::{
    Expression, BinOp, UnOp, VectorOp, ConstantValue, LetPattern,
    VariableRegistry, TheoremProgram, TheoremModuleID, Block, Statement,
    TheoremFunctionID,
};
use intermediate_theorem_format::analysis::PurityMap;
use std::collections::BTreeSet;
use super::type_renderer::{render_type, uint_cast_func, uint_type_name};
use super::statement_renderer::render_stmt;
use super::lean_writer::LeanWriter;
use crate::escape;

/// Extract variable names from expression, preserving tuple order.
/// For Tuple expressions, extracts immediate Var children in order.
/// For single Var, returns just that var.
fn extract_top_level_vars(expr: &Expression) -> Vec<String> {
    match expr {
        Expression::Tuple(exprs) => {
            exprs.iter()
                .filter_map(|e| match e {
                    Expression::Var(name) => Some(name.clone()),
                    _ => None,
                })
                .collect()
        }
        Expression::Var(name) => vec![name.clone()],
        _ => expr.iter_vars().map(|s| s.to_string()).collect(),
    }
}

/// Rendering context - holds references needed during rendering.
pub struct RenderCtx<'a> {
    pub registry: &'a VariableRegistry,
    pub program: &'a TheoremProgram,
    pub current_module_id: TheoremModuleID,
    pub current_module_namespace: Option<&'a str>,
    /// Set of variable names that are actually used in the function body.
    /// Used to generate `_` for unused bindings to avoid Lean warnings.
    pub used_vars: &'a BTreeSet<String>,
    /// Purity map - whether each function is pure (cannot abort)
    pub purity: &'a PurityMap,
    /// Whether the current function is pure (doesn't use do/pure/Except)
    pub current_function_pure: bool,
}

impl<'a> RenderCtx<'a> {
    /// Check if a function is pure based on the purity analysis.
    /// Pure functions return their value directly (no Except wrapper).
    pub fn is_function_pure(&self, func_id: TheoremFunctionID) -> bool {
        self.purity.get(&func_id).copied().unwrap_or(false)
    }

    /// Check if an expression is monadic (requires ← binding) based on purity analysis.
    /// This replaces the static `Expression::is_monadic()` with dynamic purity checking.
    pub fn is_expr_monadic(&self, expr: &Expression) -> bool {
        match expr {
            Expression::Call { function, .. } => !self.is_function_pure(*function),
            Expression::WhileExpr { .. } => true,
            Expression::IfExpr { condition, then_block, else_block } => {
                // If condition contains monadic calls, the if needs `do` wrapper and becomes monadic
                self.contains_monadic(condition)
                    || self.is_block_monadic(then_block)
                    || self.is_block_monadic(else_block)
                    || self.contains_monadic(&then_block.result)
                    || self.contains_monadic(&else_block.result)
            }
            _ => false,
        }
    }

    /// Check if an expression contains any monadic subexpressions based on purity.
    pub fn contains_monadic(&self, expr: &Expression) -> bool {
        if self.is_expr_monadic(expr) {
            return true;
        }
        match expr {
            Expression::BinOp { lhs, rhs, .. } => {
                self.contains_monadic(lhs) || self.contains_monadic(rhs)
            }
            Expression::UnOp { operand, .. } => self.contains_monadic(operand),
            Expression::Cast { value, .. } => self.contains_monadic(value),
            Expression::Call { args, .. } => args.iter().any(|a| self.contains_monadic(a)),
            Expression::Pack { fields, .. } => fields.iter().any(|f| self.contains_monadic(f)),
            Expression::FieldAccess { operand, .. } => self.contains_monadic(operand),
            Expression::Unpack { operand, .. } => self.contains_monadic(operand),
            Expression::VecOp { operands, .. } => operands.iter().any(|o| self.contains_monadic(o)),
            Expression::Tuple(exprs) => exprs.iter().any(|e| self.contains_monadic(e)),
            Expression::IfExpr { condition, then_block, else_block } => {
                self.contains_monadic(condition)
                    || self.is_block_monadic(then_block)
                    || self.is_block_monadic(else_block)
            }
            Expression::WhileExpr { condition, body } => {
                self.is_block_monadic(condition) || self.is_block_monadic(body)
            }
            Expression::Var(_) | Expression::Constant(_) => false,
        }
    }

    /// Check if a block is monadic based on purity.
    pub fn is_block_monadic(&self, block: &Block) -> bool {
        block.statements.iter().any(|s| self.is_stmt_monadic(s))
            || self.is_expr_monadic(&block.result)
    }

    /// Check if a statement is monadic based on purity.
    fn is_stmt_monadic(&self, stmt: &Statement) -> bool {
        match stmt {
            Statement::Let { value, .. } => self.is_expr_monadic(value),
            Statement::Return { values } => values.iter().any(|v| self.is_expr_monadic(v)),
            Statement::Abort { .. } => true, // Abort is always monadic
            Statement::UpdateField { target, new_value, .. } => {
                self.is_expr_monadic(target) || self.is_expr_monadic(new_value)
            }
            Statement::UpdateVectorElement { target, index, new_value } => {
                self.is_expr_monadic(target) || self.is_expr_monadic(index) || self.is_expr_monadic(new_value)
            }
            Statement::Requires { condition } | Statement::Ensures { condition } => {
                self.is_expr_monadic(condition)
            }
            Statement::Sequence(stmts) => stmts.iter().any(|s| self.is_stmt_monadic(s)),
        }
    }
}

/// Render an expression to Lean syntax.
pub fn render_expr<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    match expr {
        Expression::Var(name) => {
            write!(w, "{}", escape::escape_identifier(name)).unwrap();
        }

        Expression::Constant(value) => {
            render_constant(value, w);
        }

        Expression::BinOp { op, lhs, rhs } => {
            render_binop(*op, lhs, rhs, ctx, w);
        }

        Expression::UnOp { op, operand } => {
            render_unop(*op, operand, ctx, w);
        }

        Expression::Cast { value, target_type } => {
            use intermediate_theorem_format::TheoremType;
            if let TheoremType::UInt(bits) = target_type {
                // Method call syntax: expr.toUIntN
                // Need parens around expr if not atomic; monadic needs (← ...)
                render_expr_atomic_monadic(value, ctx, w);
                write!(w, ".{}", uint_cast_func(*bits as usize)).unwrap();
            } else {
                // Generic cast: (cast expr : Type)
                write!(w, "(cast ").unwrap();
                render_expr_atomic_monadic(value, ctx, w);
                write!(w, " : ").unwrap();
                render_type(target_type, &ctx.program.name_manager, ctx.current_module_namespace, w);
                write!(w, ")").unwrap();
            }
        }

        Expression::Call { function, args, type_args, .. } => {
            let func_name = ctx.program.get_function(*function)
                .map(|func| {
                    let escaped = escape::escape_identifier(&func.name);
                    if func.module_id == ctx.current_module_id {
                        escaped
                    } else if let Some(module) = ctx.program.get_module(func.module_id) {
                        let namespace = escape::module_name_to_namespace(&module.name);
                        format!("{}.{}", namespace, escaped)
                    } else {
                        escaped
                    }
                })
                .unwrap_or_else(|| format!("func_{}", function));

            // Render function call: func arg1 arg2 ...
            // Parens are added by the caller if needed (e.g., when used as argument)
            write!(w, "{}", func_name).unwrap();
            for ty in type_args {
                write!(w, " ").unwrap();
                render_type(ty, &ctx.program.name_manager, ctx.current_module_namespace, w);
            }
            for arg in args {
                write!(w, " ").unwrap();
                // Arguments need to be atomic; monadic args get ← wrapper
                render_expr_atomic_monadic(arg, ctx, w);
            }
        }

        Expression::Pack { struct_id, type_args, fields } => {
            let struct_def = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct definition for ID: {}", struct_id));
            let struct_name = escape::escape_struct_name(&struct_def.name);

            // Render as: StructName.mk arg1 arg2 ...
            write!(w, "{}.mk", struct_name).unwrap();
            for ty in type_args {
                write!(w, " ").unwrap();
                render_type(ty, &ctx.program.name_manager, ctx.current_module_namespace, w);
            }
            for field in fields {
                write!(w, " ").unwrap();
                render_expr_atomic_monadic(field, ctx, w);
            }
        }

        Expression::FieldAccess { struct_id, field_index, operand } => {
            let struct_def = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct definition for ID: {}", struct_id));
            let struct_name = escape::escape_struct_name(&struct_def.name);
            let field = &struct_def.fields[*field_index];
            let field_name = escape::escape_identifier(&field.name);

            // Render as: StructName.field operand
            write!(w, "{}.{} ", struct_name, field_name).unwrap();
            render_expr_atomic_monadic(operand, ctx, w);
        }

        Expression::Unpack { struct_id, operand } => {
            let struct_def = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct definition for ID: {}", struct_id));
            let struct_name = escape::escape_struct_name(&struct_def.name);

            // Render as tuple of field accesses: (S.f1 op, S.f2 op, ...)
            write!(w, "(").unwrap();
            for (i, field) in struct_def.fields.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ").unwrap();
                }
                write!(w, "{}.{} ", struct_name, escape::escape_identifier(&field.name)).unwrap();
                render_expr_atomic_monadic(operand, ctx, w);
            }
            write!(w, ")").unwrap();
        }

        Expression::VecOp { op, operands } => {
            render_vec_op(*op, operands, ctx, w);
        }

        Expression::Tuple(exprs) => {
            if exprs.is_empty() {
                write!(w, "()").unwrap();
            } else if exprs.len() == 1 {
                // Single-element "tuple" - just render the element
                // Use monadic wrapper for consistency
                render_expr_maybe_monadic(&exprs[0], ctx, w);
            } else {
                // Multi-element tuple: (e1, e2, ...)
                write!(w, "(").unwrap();
                for (i, e) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ").unwrap();
                    }
                    // Each element may be monadic; use ← if so
                    render_expr_maybe_monadic(e, ctx, w);
                }
                write!(w, ")").unwrap();
            }
        }

        Expression::IfExpr { condition, then_block, else_block } => {
            // Check for short-circuit And pattern: if c1 then c2 else false => c1 && c2
            if let Some(and_expr) = try_simplify_short_circuit_and(condition, then_block, else_block, ctx) {
                // Use monadic wrappers - adds (← ...) for monadic operands
                render_expr_atomic_monadic(condition, ctx, w);
                write!(w, " && ").unwrap();
                render_expr_atomic_monadic(&and_expr, ctx, w);
                return;
            }

            // Check for short-circuit Or pattern: if c1 then true else c2 => c1 || c2
            if let Some(or_expr) = try_simplify_short_circuit_or(condition, then_block, else_block, ctx) {
                // Use monadic wrappers - adds (← ...) for monadic operands
                render_expr_atomic_monadic(condition, ctx, w);
                write!(w, " || ").unwrap();
                render_expr_atomic_monadic(&or_expr, ctx, w);
                return;
            }

            // Inline if expression: (if cond then block else block)
            // Both branches must have the same type, so if either is monadic, both must be
            // Also check contains_monadic for inlined monadic subexpressions
            let then_has_monadic = ctx.is_block_monadic(then_block)
                || ctx.contains_monadic(&then_block.result);
            let else_has_monadic = ctx.is_block_monadic(else_block)
                || ctx.contains_monadic(&else_block.result);
            let either_monadic = then_has_monadic || else_has_monadic;

            // If condition OR any branch result contains monadic calls, need `do` wrapper
            let condition_is_monadic = ctx.is_expr_monadic(condition);
            let condition_has_monadic = ctx.contains_monadic(condition);
            let needs_do = condition_is_monadic || condition_has_monadic || either_monadic;
            if needs_do {
                write!(w, "(do if ").unwrap();
            } else {
                write!(w, "(if ").unwrap();
            }
            // If condition is a monadic call, add ← prefix to bind it
            render_expr_maybe_monadic(condition, ctx, w);
            write!(w, " then ").unwrap();
            render_block_inline_with_context(then_block, needs_do, ctx, w);
            write!(w, " else ").unwrap();
            render_block_inline_with_context(else_block, needs_do, ctx, w);
            write!(w, ")").unwrap();
        }

        Expression::WhileExpr { condition, body } => {
            // Inline while: (whileLoop (fun s => cond_block) (fun s => body_block) init)
            // Derive state variables from body result (preserving tuple order)
            let state_vars = extract_top_level_vars(&body.result);
            let state_pattern = make_pattern(&state_vars);

            // Initial values are just the same variable names (referencing outer scope)
            let init_str = if state_vars.is_empty() {
                "()".to_string()
            } else if state_vars.len() == 1 {
                crate::escape::escape_identifier(&state_vars[0])
            } else {
                let vals: Vec<_> = state_vars.iter().map(|v| crate::escape::escape_identifier(v)).collect();
                format!("({})", vals.join(", "))
            };

            let mut cond_str = String::new();
            render_block_inline(condition, ctx, &mut cond_str);

            let mut body_str = String::new();
            render_block_inline(body, ctx, &mut body_str);

            write!(w, "(whileLoop (fun {} => {}) (fun {} => {}) {})",
                state_pattern, cond_str, state_pattern, body_str, init_str).unwrap();
        }
    }
}

/// Render a block inline as a single expression.
/// For pure blocks: uses `(let x := e in result)` syntax
/// For monadic blocks: uses `(do let x ← e; result)` syntax
fn render_block_inline<W: Write>(block: &Block, ctx: &RenderCtx, w: &mut W) {
    let need_monadic = ctx.is_block_monadic(block) || ctx.contains_monadic(&block.result);
    render_block_inline_with_context(block, need_monadic, ctx, w);
}

/// Render a block inline with explicit monadic context.
/// When `need_monadic` is true, renders using `do` notation.
/// When false, renders using `Id.run do` for pure blocks.
fn render_block_inline_with_context<W: Write>(block: &Block, need_monadic: bool, ctx: &RenderCtx, w: &mut W) {
    let block_is_monadic = ctx.is_block_monadic(block);
    // Also check if result contains monadic subexpressions (after inlining)
    let result_contains_monadic = ctx.contains_monadic(&block.result);

    if block.statements.is_empty() {
        // No statements - just render result
        if ctx.is_expr_monadic(&block.result) {
            // Result is monadic - render directly (no pure wrapper)
            render_expr(&block.result, ctx, w);
        } else if need_monadic {
            // Result is pure but we need monadic - wrap with pure
            // If result contains_monadic, the ← bindings are inside, but result is still pure
            write!(w, "pure ").unwrap();
            render_expr_atomic(&block.result, ctx, w);
        } else {
            // Pure context, pure result - render directly
            render_expr(&block.result, ctx, w);
        }
    } else if need_monadic || block_is_monadic || result_contains_monadic {
        // Monadic block - use do notation
        write!(w, "(do ").unwrap();

        // Use inline writer for statements
        let mut inline_writer = LeanWriter::new_inline(String::new());
        for stmt in &block.statements {
            render_stmt(stmt, ctx, &mut inline_writer);
            inline_writer.write("\n"); // becomes "; " in inline mode
        }
        write!(w, "{}", inline_writer.into_inner()).unwrap();

        if ctx.is_expr_monadic(&block.result) {
            // Result is monadic - render directly
            render_expr(&block.result, ctx, w);
        } else {
            // Result is pure - wrap with pure
            write!(w, "pure ").unwrap();
            render_expr_atomic(&block.result, ctx, w);
        }
        write!(w, ")").unwrap();
    } else {
        // Pure block in pure context - use Id.run do
        write!(w, "(").unwrap();
        render_pure_lets_inline(block, ctx, w);
        write!(w, ")").unwrap();
    }
}

/// Render pure Let statements inline using `Id.run do` syntax for Lean 4
/// This allows using `let` statements in a pure context
fn render_pure_lets_inline<W: Write>(block: &Block, ctx: &RenderCtx, w: &mut W) {
    write!(w, "Id.run do ").unwrap();
    for stmt in &block.statements {
        if let Statement::Let { pattern, value, .. } = stmt {
            let pattern_str = render_let_pattern(pattern);
            write!(w, "let {} := ", pattern_str).unwrap();
            render_expr(value, ctx, w);
            write!(w, "; ").unwrap();
        }
        // Skip non-Let statements in pure context (shouldn't happen)
    }
    write!(w, "pure ").unwrap();
    render_expr_atomic(&block.result, ctx, w);
}

/// Render a LetPattern to a string
fn render_let_pattern(pattern: &LetPattern) -> String {
    match pattern {
        LetPattern::Single(name) => escape::escape_identifier(name),
        LetPattern::Tuple(names) => {
            if names.is_empty() {
                "_".to_string()
            } else {
                let escaped: Vec<_> = names.iter().map(|n| escape::escape_identifier(n)).collect();
                format!("({})", escaped.join(", "))
            }
        }
    }
}

/// Render a constant value.
fn render_constant<W: Write>(value: &ConstantValue, w: &mut W) {
    match value {
        ConstantValue::Bool(b) => write!(w, "{}", if *b { "true" } else { "false" }).unwrap(),
        ConstantValue::UInt { bits, value: v } => {
            // UInt8 and UInt128 need type annotations for operations where type is ambiguous
            // UInt8: shift amounts
            // UInt128: large constants used with shift/bitwise ops
            if *bits == 8 || *bits == 128 {
                write!(w, "({} : {})", v, uint_type_name(*bits)).unwrap();
            } else {
                write!(w, "{}", v).unwrap();
            }
        }
        ConstantValue::Address(addr) => write!(w, "{}", addr).unwrap(),
        ConstantValue::Vector(elements) => {
            write!(w, "[").unwrap();
            for (i, e) in elements.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ").unwrap();
                }
                render_constant(e, w);
            }
            write!(w, "]").unwrap();
        }
    }
}

/// Render a constant value with explicit type annotation.
/// Used for contexts where type inference fails (e.g., shift amounts).
fn render_constant_with_type<W: Write>(value: &ConstantValue, w: &mut W) {
    match value {
        ConstantValue::Bool(b) => write!(w, "{}", if *b { "true" } else { "false" }).unwrap(),
        ConstantValue::UInt { bits, value: v } => {
            write!(w, "({} : {})", v, uint_type_name(*bits)).unwrap();
        }
        ConstantValue::Address(addr) => write!(w, "{}", addr).unwrap(),
        ConstantValue::Vector(elements) => {
            write!(w, "[").unwrap();
            for (i, e) in elements.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ").unwrap();
                }
                render_constant_with_type(e, w);
            }
            write!(w, "]").unwrap();
        }
    }
}

/// Render an expression with type annotations for constants.
/// Used for contexts where type inference needs help (e.g., shift amounts).
fn render_expr_with_type<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    match expr {
        Expression::Constant(value) => render_constant_with_type(value, w),
        // For non-constants, use atomic rendering
        _ => render_expr_atomic(expr, ctx, w),
    }
}

/// Render an expression with type annotations, wrapping in parens if not atomic.
/// Used for shift LHS where the type determines the result type.
/// In pure functions, never uses `←` since there's no do block.
fn render_expr_with_type_atomic<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    match expr {
        Expression::Constant(value) => render_constant_with_type(value, w),
        // For monadic expressions in non-pure context, add ← prefix
        _ if !ctx.current_function_pure && ctx.is_expr_monadic(expr) => {
            write!(w, "(← ").unwrap();
            render_expr(expr, ctx, w);
            write!(w, ")").unwrap();
        }
        _ => render_expr_atomic(expr, ctx, w),
    }
}

/// Render a binary operation.
/// Renders without outer parens - caller adds parens if needed via render_expr_atomic.
fn render_binop<W: Write>(op: BinOp, lhs: &Expression, rhs: &Expression, ctx: &RenderCtx, w: &mut W) {
    // Comparison ops need `decide` wrapper for Bool conversion
    let is_comparison = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
    // Shift ops need typed operands (LHS determines result type, RHS is shift amount)
    let is_shift = matches!(op, BinOp::Shl | BinOp::Shr);

    if is_comparison {
        write!(w, "decide (").unwrap();
    }

    // Shift LHS needs type annotation when it's a constant
    if is_shift {
        render_expr_with_type_atomic(lhs, ctx, w);
    } else {
        // Use monadic wrapper - adds (← ...) for monadic operands
        render_expr_atomic_monadic(lhs, ctx, w);
    }

    let infix = match op {
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::Div => " / ",
        BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ",
        BinOp::BitOr => " ||| ",
        BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ",
        BinOp::Shr => " >>> ",
        BinOp::And => " && ",
        BinOp::Or => " || ",
        BinOp::Eq => " == ",
        BinOp::Neq => " != ",
        BinOp::Lt => " < ",
        BinOp::Le => " ≤ ",
        BinOp::Gt => " > ",
        BinOp::Ge => " ≥ ",
    };
    write!(w, "{}", infix).unwrap();

    // Shift RHS needs type annotation for the shift amount
    if is_shift {
        render_expr_with_type(rhs, ctx, w);
    } else {
        // Use monadic wrapper - adds (← ...) for monadic operands
        render_expr_atomic_monadic(rhs, ctx, w);
    }

    if is_comparison {
        write!(w, ")").unwrap();
    }
}

/// Render a unary operation.
/// Not renders as `!expr`, casts render as `toUIntN expr`.
fn render_unop<W: Write>(op: UnOp, operand: &Expression, ctx: &RenderCtx, w: &mut W) {
    match op {
        UnOp::Not => {
            write!(w, "!").unwrap();
            // Use monadic wrapper - adds (← ...) for monadic operands
            render_expr_atomic_monadic(operand, ctx, w);
        }
        UnOp::CastU8 | UnOp::CastU16 | UnOp::CastU32 | UnOp::CastU64 | UnOp::CastU128 | UnOp::CastU256 => {
            let bits = match op {
                UnOp::CastU8 => 8,
                UnOp::CastU16 => 16,
                UnOp::CastU32 => 32,
                UnOp::CastU64 => 64,
                UnOp::CastU128 => 128,
                UnOp::CastU256 => 256,
                _ => unreachable!(),
            };
            write!(w, "{} ", uint_cast_func(bits)).unwrap();
            // Use monadic wrapper - adds (← ...) for monadic operands
            render_expr_atomic_monadic(operand, ctx, w);
        }
    }
}

/// Render a vector operation.
/// These render as function calls: List.func arg1 arg2 ...
fn render_vec_op<W: Write>(op: VectorOp, operands: &[Expression], ctx: &RenderCtx, w: &mut W) {
    match op {
        VectorOp::Empty => write!(w, "List.nil").unwrap(),
        VectorOp::Length => {
            write!(w, "List.length ").unwrap();
            render_expr_atomic_monadic(&operands[0], ctx, w);
        }
        VectorOp::Push => {
            write!(w, "List.concat ").unwrap();
            render_expr_atomic_monadic(&operands[0], ctx, w);
            write!(w, " [").unwrap();
            render_expr(&operands[1], ctx, w);
            write!(w, "]").unwrap();
        }
        VectorOp::Pop => {
            write!(w, "List.dropLast ").unwrap();
            render_expr_atomic_monadic(&operands[0], ctx, w);
        }
        VectorOp::Borrow | VectorOp::BorrowMut => {
            write!(w, "List.get! ").unwrap();
            render_expr_atomic_monadic(&operands[0], ctx, w);
            write!(w, " ").unwrap();
            render_expr_atomic_monadic(&operands[1], ctx, w);
        }
        VectorOp::Swap => {
            write!(w, "List.swap ").unwrap();
            render_expr_atomic_monadic(&operands[0], ctx, w);
            write!(w, " ").unwrap();
            render_expr_atomic_monadic(&operands[1], ctx, w);
            write!(w, " ").unwrap();
            render_expr_atomic_monadic(&operands[2], ctx, w);
        }
    }
}

/// Make a binding pattern from variable names.
pub fn make_pattern(names: &[String]) -> String {
    if names.is_empty() {
        "_".to_string()
    } else if names.len() == 1 {
        let name = &names[0];
        if name == "()" { "_".to_string() } else { escape::escape_identifier(name) }
    } else {
        let escaped: Vec<_> = names.iter()
            .map(|name| {
                if name == "()" { "_".to_string() } else { escape::escape_identifier(name) }
            })
            .collect();
        format!("({})", escaped.join(", "))
    }
}

/// Make a binding pattern, using `_` for names that are not in the used set.
/// This is used for while loop result bindings where some results may be unused.
pub fn make_pattern_with_used(names: &[String], used: &BTreeSet<String>) -> String {
    if names.is_empty() {
        "_".to_string()
    } else if names.len() == 1 {
        if !used.contains(&names[0]) {
            "_".to_string()
        } else {
            let name = &names[0];
            if name == "()" { "_".to_string() } else { escape::escape_identifier(name) }
        }
    } else {
        let escaped: Vec<_> = names.iter()
            .map(|name| {
                if !used.contains(name) {
                    "_".to_string()
                } else {
                    if name == "()" { "_".to_string() } else { escape::escape_identifier(name) }
                }
            })
            .collect();
        format!("({})", escaped.join(", "))
    }
}

/// Render a tuple or single expression.
fn render_tuple_or_single<W: Write>(exprs: &[Expression], ctx: &RenderCtx, w: &mut W) {
    if exprs.is_empty() {
        write!(w, "()").unwrap();
    } else if exprs.len() == 1 {
        render_expr(&exprs[0], ctx, w);
    } else {
        write!(w, "(").unwrap();
        for (i, e) in exprs.iter().enumerate() {
            if i > 0 {
                write!(w, ", ").unwrap();
            }
            render_expr(e, ctx, w);
        }
        write!(w, ")").unwrap();
    }
}

/// Render an expression to a string.
pub fn expr_to_string(expr: &Expression, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_expr(expr, ctx, &mut s);
    s
}

/// Render an expression to a string, wrapping in parens if not atomic.
/// Use this when the expression is an argument to a function like `pure`.
/// Does NOT add `←` for monadic expressions.
pub fn expr_to_string_atomic(expr: &Expression, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_expr_atomic(expr, ctx, &mut s);
    s
}

/// Render an expression to a string, wrapping in parens if not atomic, adding `←` if monadic.
/// Use this when in a do block and monadic calls should be bound.
pub fn expr_to_string_atomic_monadic(expr: &Expression, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_expr_atomic_monadic(expr, ctx, &mut s);
    s
}

/// Render an expression to a string, adding  prefix if monadic.
/// Use this for if-conditions in a do block where monadic calls should be bound.
/// Adds parens around the expression only if needed for grouping.
pub fn expr_to_string_maybe_monadic(expr: &Expression, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_expr_maybe_monadic(expr, ctx, &mut s);
    s
}

/// Render an expression that may need monadic wrapping.
/// When the expression is monadic (e.g., a Call with non-Pure convention),
/// and it appears as an argument to another expression (inlined),
/// it needs to be wrapped with . Parens are only added if needed.
/// In pure functions, never use `←` since there's no do block.
fn render_expr_maybe_monadic<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    // In pure functions, never use ← syntax
    if ctx.current_function_pure {
        render_expr(expr, ctx, w);
    } else if ctx.is_expr_monadic(expr) {
        write!(w, "← ").unwrap();
        // Render with parens only if it's a complex expression that needs grouping
        render_expr_atomic(expr, ctx, w);
    } else {
        render_expr(expr, ctx, w);
    }
}

/// Check if an expression is "atomic" (doesn't need parens when used as an argument).
/// Atomic expressions: variables, constants, tuples (which have parens), nullary calls/ops.
fn is_atomic(expr: &Expression) -> bool {
    match expr {
        Expression::Var(_) | Expression::Constant(_) | Expression::Tuple(_) => true,
        // Nullary calls don't need parens, but calls with args do
        Expression::Call { args, type_args, .. } => args.is_empty() && type_args.is_empty(),
        // Pack and FieldAccess render as function calls - not atomic if they have args
        Expression::Pack { fields, .. } => fields.is_empty(),
        Expression::FieldAccess { .. } => false, // Always has an operand
        // VecOp - Empty is atomic, others are not
        Expression::VecOp { op, .. } => matches!(op, VectorOp::Empty),
        // Unpack is a tuple of field accesses - not atomic
        Expression::Unpack { .. } => false,
        // Operators and complex expressions need parens
        _ => false,
    }
}

/// Render an expression, wrapping in parens if it's not atomic.
/// Does NOT add `←` for monadic expressions - use render_expr_atomic_monadic for that.
fn render_expr_atomic<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    if is_atomic(expr) {
        render_expr(expr, ctx, w);
    } else {
        write!(w, "(").unwrap();
        render_expr(expr, ctx, w);
        write!(w, ")").unwrap();
    }
}

/// Render an expression, wrapping in parens if not atomic, and adding `←` if monadic.
/// Use this when the expression is an argument position within a do block.
/// In pure functions, never use `←` since there's no do block.
fn render_expr_atomic_monadic<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    // In pure functions, never use ← syntax
    if ctx.current_function_pure {
        render_expr_atomic(expr, ctx, w);
    } else if ctx.is_expr_monadic(expr) {
        // Monadic expressions need `← ` prefix when used as arguments in do blocks
        write!(w, "(← ").unwrap();
        render_expr(expr, ctx, w);
        write!(w, ")").unwrap();
    } else {
        render_expr_atomic(expr, ctx, w);
    }
}

/// Check if an expression is a boolean constant (directly or via a simple temp)
fn is_bool_constant(expr: &Expression, expected: bool, _ctx: &RenderCtx) -> bool {
    match expr {
        Expression::Constant(ConstantValue::Bool(b)) => *b == expected,
        // Note: We can't easily look through temps to their definitions here because
        // the definitions are stored in TempUsageInfo which isn't available at render time.
        // The temp inlining pass should handle this for single-use temps.
        // For multi-use temps that hold boolean constants, we accept the limitation.
        _ => false,
    }
}

/// Try to simplify short-circuit And pattern: if c1 then c2 else false => c1 && c2
/// Returns Some(c2) if the pattern matches, None otherwise.
fn try_simplify_short_circuit_and(_condition: &Expression, then_block: &Block, else_block: &Block, ctx: &RenderCtx) -> Option<Expression> {
    // else_block must be just `false` with no statements
    if !else_block.statements.is_empty() {
        return None;
    }
    if !is_bool_constant(&else_block.result, false, ctx) {
        return None;
    }

    // then_block must be just a simple expression with no statements
    if !then_block.statements.is_empty() {
        return None;
    }

    Some((*then_block.result).clone())
}

/// Try to simplify short-circuit Or pattern: if c1 then true else c2 => c1 || c2
/// Returns Some(c2) if the pattern matches, None otherwise.
fn try_simplify_short_circuit_or(_condition: &Expression, then_block: &Block, else_block: &Block, ctx: &RenderCtx) -> Option<Expression> {
    // then_block must be just `true` with no statements
    if !then_block.statements.is_empty() {
        return None;
    }
    if !is_bool_constant(&then_block.result, true, ctx) {
        return None;
    }

    // else_block must be just a simple expression with no statements
    if !else_block.statements.is_empty() {
        return None;
    }

    Some((*else_block.result).clone())
}
