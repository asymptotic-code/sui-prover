// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders IR to Lean syntax.
//! Pure translation - pattern match IR nodes to Lean text.

use super::lean_writer::LeanWriter;
use super::statement_renderer::render_stmt;
use super::type_renderer::{render_type, uint_cast_func, uint_type_name};
use crate::escape;
use intermediate_theorem_format::{
    BinOp, Const, IRNode, ModuleID, Program, UnOp, VariableRegistry, VecOp,
};
use std::fmt::Write;

/// Rendering context - holds references needed during rendering.
pub struct RenderCtx<'a> {
    pub registry: &'a VariableRegistry,
    pub program: &'a Program,
    pub current_module_id: ModuleID,
    pub current_module_namespace: Option<&'a str>,
    /// Whether the current function is monadic (uses do/Except)
    pub current_function_monadic: bool,
}

impl<'a> RenderCtx<'a> {
    /// Returns whether a function is monadic (returns Except) by checking its signature.
    pub fn is_func_monadic(&self, func_id: intermediate_theorem_format::FunctionID) -> bool {
        self.program
            .functions
            .get(func_id)
            .signature
            .return_type
            .is_monad()
    }
}

/// Check if an IR node is a monadic expression (directly returns Except).
/// Delegates to the IR's is_monadic method.
fn is_call_monadic(ir: &IRNode, ctx: &RenderCtx) -> bool {
    ir.is_monadic(&|fid| ctx.is_func_monadic(fid))
}

/// Check if an IR node contains any monadic call anywhere in its tree.
/// Delegates to the IR's contains_monadic method.
pub fn contains_call_monadic(ir: &IRNode, ctx: &RenderCtx) -> bool {
    ir.contains_monadic(&|fid| ctx.is_func_monadic(fid))
}

/// Render an IR node to Lean syntax.
pub fn render_ir<W: Write>(ir: &IRNode, ctx: &RenderCtx, w: &mut W) {
    match ir {
        IRNode::Var(name) => {
            write!(w, "{}", escape::escape_identifier(name)).unwrap();
        }

        IRNode::Const(value) => {
            render_constant(value, false, w);
        }

        IRNode::BinOp { op, lhs, rhs } => {
            render_binop(*op, lhs, rhs, ctx, w);
        }

        IRNode::UnOp { op, operand } => {
            render_unop(*op, operand, ctx, w);
        }

        IRNode::Call {
            function,
            args,
            type_args,
            ..
        } => {
            let func = ctx.program.functions.get(*function);
            let escaped = escape::escape_identifier(&func.name);
            let func_name = if func.module_id == ctx.current_module_id {
                escaped
            } else {
                let module = ctx.program.modules.get(func.module_id);
                let namespace = escape::module_name_to_namespace(&module.name);
                format!("{}.{}", namespace, escaped)
            };

            write!(w, "{}", func_name).unwrap();
            for ty in type_args {
                write!(w, " ").unwrap();
                render_type(ty, ctx.program, ctx.current_module_namespace, w);
            }
            for arg in args {
                write!(w, " ").unwrap();
                render_ir_atomic_monadic(arg, ctx, w);
            }
        }

        IRNode::Pack {
            struct_id,
            type_args,
            fields,
        } => {
            let struct_def = ctx.program.structs.get(struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);

            write!(w, "{}.mk", struct_name).unwrap();
            for ty in type_args {
                write!(w, " ").unwrap();
                render_type(ty, ctx.program, ctx.current_module_namespace, w);
            }
            for field in fields {
                write!(w, " ").unwrap();
                render_ir_atomic_monadic(field, ctx, w);
            }
        }

        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => {
            let struct_def = ctx.program.structs.get(struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);
            let field = &struct_def.fields[*field_index];
            let field_name = escape::escape_identifier(&field.name);

            write!(w, "{}.{} ", struct_name, field_name).unwrap();
            render_ir_atomic_monadic(base, ctx, w);
        }

        IRNode::Unpack { struct_id, value } => {
            let struct_def = ctx.program.structs.get(struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);

            write!(w, "(").unwrap();
            for (i, field) in struct_def.fields.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ").unwrap();
                }
                write!(
                    w,
                    "{}.{} ",
                    struct_name,
                    escape::escape_identifier(&field.name)
                )
                .unwrap();
                render_ir_atomic_monadic(value, ctx, w);
            }
            write!(w, ")").unwrap();
        }

        IRNode::VecOp { op, args } => {
            render_vec_op(*op, args, ctx, w);
        }

        IRNode::Tuple(elems) => {
            if elems.is_empty() {
                write!(w, "()").unwrap();
            } else if elems.len() == 1 {
                render_ir_maybe_monadic(&elems[0], ctx, w);
            } else {
                let has_monadic = elems.iter().any(|e| is_call_monadic(e, ctx));
                if has_monadic && ctx.current_function_monadic {
                    // Need to sequence monadic elements: (← e1, e2) becomes do let x ← e1; pure (x, e2)
                    write!(w, "(do ").unwrap();
                    let mut temp_names = Vec::new();
                    for (i, e) in elems.iter().enumerate() {
                        if is_call_monadic(e, ctx) {
                            let temp_name = format!("__tuple_elem_{}", i);
                            write!(w, "let {} ← ", temp_name).unwrap();
                            render_ir(e, ctx, w);
                            write!(w, "; ").unwrap();
                            temp_names.push(temp_name);
                        } else {
                            temp_names.push(String::new()); // Placeholder for non-monadic
                        }
                    }
                    write!(w, "pure (").unwrap();
                    for (i, e) in elems.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ").unwrap();
                        }
                        if !temp_names[i].is_empty() {
                            write!(w, "{}", temp_names[i]).unwrap();
                        } else {
                            render_ir(e, ctx, w);
                        }
                    }
                    write!(w, "))").unwrap();
                } else {
                    write!(w, "(").unwrap();
                    for (i, e) in elems.iter().enumerate() {
                        if i > 0 {
                            write!(w, ", ").unwrap();
                        }
                        render_ir(e, ctx, w);
                    }
                    write!(w, ")").unwrap();
                }
            }
        }

        IRNode::Block { children } => {
            // A block as an expression - render inline
            render_block_inline(children, ctx, w);
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Inline if expression - need do block if any part contains monadic operations
            let needs_do = contains_call_monadic(cond, ctx)
                || contains_call_monadic(then_branch, ctx)
                || contains_call_monadic(else_branch, ctx);

            if needs_do {
                write!(w, "(do if ").unwrap();
            } else {
                write!(w, "(if ").unwrap();
            }
            render_ir_maybe_monadic(cond, ctx, w);
            write!(w, " then ").unwrap();
            render_branch_inline(then_branch, needs_do, ctx, w);
            write!(w, " else ").unwrap();
            render_branch_inline(else_branch, needs_do, ctx, w);
            write!(w, ")").unwrap();
        }

        IRNode::While { cond, body, vars } => {
            // Inline while: (whileLoop (fun s => cond_block) (fun s => body_block) init)
            // whileLoop is monadic - the condition and body functions must return Except
            let state_pattern = make_pattern(vars);
            let init_str = super::render_tuple_like(vars, "()", ", ", |v| {
                if v.starts_with("$t") {
                    "default".to_string()
                } else {
                    escape::escape_identifier(v)
                }
            });

            let mut cond_str = String::new();
            // Condition must return Except AbortCode Bool, so need_monadic=true
            render_branch_inline(cond, true, ctx, &mut cond_str);

            let mut body_str = String::new();
            // Body must return Except AbortCode state, so need_monadic=true
            render_branch_inline(body, true, ctx, &mut body_str);

            write!(
                w,
                "(whileLoop (fun {} => {}) (fun {} => {}) {})",
                state_pattern, cond_str, state_pattern, body_str, init_str
            )
            .unwrap();
        }

        // Statement-like IR nodes - render as their expression form
        IRNode::Let { pattern, value, .. } => {
            // When a Let appears as an expression (e.g., last in block), skip binding
            render_ir(value, ctx, w);
            let _ = pattern; // Pattern ignored in expression context
        }

        IRNode::Return(values) => {
            if values.is_empty() {
                write!(w, "()").unwrap();
            } else if values.len() == 1 {
                render_ir(&values[0], ctx, w);
            } else {
                write!(w, "(").unwrap();
                for (i, v) in values.iter().enumerate() {
                    if i > 0 {
                        write!(w, ", ").unwrap();
                    }
                    render_ir(v, ctx, w);
                }
                write!(w, ")").unwrap();
            }
        }

        IRNode::Abort(code) => {
            write!(w, "Except.error ").unwrap();
            render_ir_atomic(code, ctx, w);
        }

        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => {
            let struct_def = ctx.program.structs.get(struct_id);
            let field_name = &struct_def.fields[*field_index].name;
            write!(w, "{{ ").unwrap();
            render_ir(base, ctx, w);
            write!(w, " with {} := ", field_name).unwrap();
            render_ir(value, ctx, w);
            write!(w, " }}").unwrap();
        }

        IRNode::UpdateVec { base, index, value } => {
            render_ir(base, ctx, w);
            write!(w, ".set ").unwrap();
            render_ir_atomic(index, ctx, w);
            write!(w, " ").unwrap();
            render_ir_atomic(value, ctx, w);
        }

        IRNode::Requires(cond) => {
            write!(w, "-- requires: ").unwrap();
            render_ir(cond, ctx, w);
        }

        IRNode::Ensures(cond) => {
            write!(w, "-- ensures: ").unwrap();
            render_ir(cond, ctx, w);
        }
    }
}

/// Render a block (children vector) inline as a single expression.
fn render_block_inline<W: Write>(children: &[IRNode], ctx: &RenderCtx, w: &mut W) {
    if children.is_empty() {
        write!(w, "()").unwrap();
        return;
    }

    let stmts = &children[..children.len() - 1];
    let result = &children[children.len() - 1];

    let need_monadic =
        stmts.iter().any(|s| contains_call_monadic(s, ctx)) || contains_call_monadic(result, ctx);

    if stmts.is_empty() {
        if is_call_monadic(result, ctx) {
            render_ir(result, ctx, w);
        } else if need_monadic {
            write!(w, "pure ").unwrap();
            render_ir_atomic(result, ctx, w);
        } else {
            render_ir(result, ctx, w);
        }
    } else if need_monadic {
        write!(w, "(do ").unwrap();
        let mut inline_writer = LeanWriter::new_inline(String::new());
        for stmt in stmts {
            render_stmt(stmt, ctx, &mut inline_writer);
            inline_writer.write("\n");
        }
        write!(w, "{}", inline_writer.into_inner()).unwrap();

        if is_call_monadic(result, ctx) {
            render_ir(result, ctx, w);
        } else {
            write!(w, "pure ").unwrap();
            render_ir_atomic(result, ctx, w);
        }
        write!(w, ")").unwrap();
    } else {
        write!(w, "(Id.run do ").unwrap();
        for stmt in stmts {
            if let IRNode::Let { pattern, value, .. } = stmt {
                let pattern_str = render_pattern(pattern);
                write!(w, "let {} := ", pattern_str).unwrap();
                render_ir(value, ctx, w);
                write!(w, "; ").unwrap();
            }
        }
        write!(w, "pure ").unwrap();
        render_ir_atomic(result, ctx, w);
        write!(w, ")").unwrap();
    }
}

/// Render a branch (could be Block or single expression) inline
fn render_branch_inline<W: Write>(ir: &IRNode, need_monadic: bool, ctx: &RenderCtx, w: &mut W) {
    match ir {
        IRNode::Block { children } => {
            if children.is_empty() {
                if need_monadic {
                    write!(w, "pure ()").unwrap();
                } else {
                    write!(w, "()").unwrap();
                }
                return;
            }

            let stmts = &children[..children.len() - 1];
            let result = &children[children.len() - 1];

            if stmts.is_empty() {
                if is_call_monadic(result, ctx) {
                    render_ir(result, ctx, w);
                } else if need_monadic {
                    write!(w, "pure ").unwrap();
                    render_ir_atomic(result, ctx, w);
                } else {
                    render_ir(result, ctx, w);
                }
            } else {
                // Has statements - need do block
                // Use `do` if any statements or result are monadic, else `Id.run do`
                let stmts_are_monadic = stmts.iter().any(|s| contains_call_monadic(s, ctx));
                let result_is_monadic = contains_call_monadic(result, ctx);
                let block_is_monadic = need_monadic || stmts_are_monadic || result_is_monadic;

                if block_is_monadic {
                    write!(w, "(do ").unwrap();
                } else {
                    write!(w, "(Id.run do ").unwrap();
                }
                let mut inline_writer = LeanWriter::new_inline(String::new());
                for stmt in stmts {
                    render_stmt(stmt, ctx, &mut inline_writer);
                    inline_writer.write("\n");
                }
                write!(w, "{}", inline_writer.into_inner()).unwrap();

                if is_call_monadic(result, ctx) {
                    render_ir(result, ctx, w);
                } else {
                    write!(w, "pure ").unwrap();
                    render_ir_atomic(result, ctx, w);
                }
                write!(w, ")").unwrap();
            }
        }
        _ => {
            if is_call_monadic(ir, ctx) {
                render_ir(ir, ctx, w);
            } else if need_monadic {
                write!(w, "pure ").unwrap();
                render_ir_atomic(ir, ctx, w);
            } else {
                render_ir(ir, ctx, w);
            }
        }
    }
}

/// Render a pattern (Vec<String>) to a string
pub fn render_pattern(pattern: &[String]) -> String {
    make_pattern(pattern)
}

/// Render a constant value.
fn render_constant<W: Write>(value: &Const, force_type: bool, w: &mut W) {
    match value {
        Const::Bool(b) => write!(w, "{}", if *b { "true" } else { "false" }).unwrap(),
        Const::UInt { bits, value: v } => {
            if force_type || *bits == 8 || *bits == 128 {
                write!(w, "({} : {})", v, uint_type_name(*bits)).unwrap();
            } else {
                write!(w, "{}", v).unwrap();
            }
        }
        Const::Address(addr) => write!(w, "{}", addr).unwrap(),
        Const::Vector(elements) => {
            write!(w, "[").unwrap();
            for (i, e) in elements.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ").unwrap();
                }
                render_constant(e, force_type, w);
            }
            write!(w, "]").unwrap();
        }
    }
}

/// Render a binary operation.
fn render_binop<W: Write>(op: BinOp, lhs: &IRNode, rhs: &IRNode, ctx: &RenderCtx, w: &mut W) {
    let is_comparison = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
    let is_shift = matches!(op, BinOp::Shl | BinOp::Shr);

    if is_comparison {
        write!(w, "decide (").unwrap();
    }

    // Shift operations need type annotations on constants
    if is_shift {
        if let IRNode::Const(value) = lhs {
            render_constant(value, true, w);
        } else {
            render_ir_atomic_monadic(lhs, ctx, w);
        }
    } else {
        render_ir_atomic_monadic(lhs, ctx, w);
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

    if is_shift {
        if let IRNode::Const(value) = rhs {
            render_constant(value, true, w);
        } else {
            render_ir_atomic(rhs, ctx, w);
        }
    } else {
        render_ir_atomic_monadic(rhs, ctx, w);
    }

    if is_comparison {
        write!(w, ")").unwrap();
    }
}

/// Render a unary operation.
fn render_unop<W: Write>(op: UnOp, operand: &IRNode, ctx: &RenderCtx, w: &mut W) {
    match op {
        UnOp::Not => {
            write!(w, "!").unwrap();
            render_ir_atomic_monadic(operand, ctx, w);
        }
        UnOp::CastU8 => {
            render_ir_atomic_monadic(operand, ctx, w);
            write!(w, ".{}", uint_cast_func(8)).unwrap();
        }
        UnOp::CastU16 => {
            render_ir_atomic_monadic(operand, ctx, w);
            write!(w, ".{}", uint_cast_func(16)).unwrap();
        }
        UnOp::CastU32 => {
            render_ir_atomic_monadic(operand, ctx, w);
            write!(w, ".{}", uint_cast_func(32)).unwrap();
        }
        UnOp::CastU64 => {
            render_ir_atomic_monadic(operand, ctx, w);
            write!(w, ".{}", uint_cast_func(64)).unwrap();
        }
        UnOp::CastU128 => {
            render_ir_atomic_monadic(operand, ctx, w);
            write!(w, ".{}", uint_cast_func(128)).unwrap();
        }
        UnOp::CastU256 => {
            render_ir_atomic_monadic(operand, ctx, w);
            write!(w, ".{}", uint_cast_func(256)).unwrap();
        }
    }
}

/// Render a vector operation.
fn render_vec_op<W: Write>(op: VecOp, operands: &[IRNode], ctx: &RenderCtx, w: &mut W) {
    match op {
        VecOp::Empty => write!(w, "List.nil").unwrap(),
        VecOp::Length => {
            write!(w, "List.length ").unwrap();
            render_ir_atomic_monadic(&operands[0], ctx, w);
        }
        VecOp::Push => {
            write!(w, "List.concat ").unwrap();
            render_ir_atomic_monadic(&operands[0], ctx, w);
            write!(w, " [").unwrap();
            render_ir(&operands[1], ctx, w);
            write!(w, "]").unwrap();
        }
        VecOp::Pop => {
            write!(w, "List.dropLast ").unwrap();
            render_ir_atomic_monadic(&operands[0], ctx, w);
        }
        VecOp::Borrow | VecOp::BorrowMut => {
            write!(w, "List.get! ").unwrap();
            render_ir_atomic_monadic(&operands[0], ctx, w);
            write!(w, " ").unwrap();
            render_ir_atomic_monadic(&operands[1], ctx, w);
        }
        VecOp::Swap => {
            write!(w, "List.swap ").unwrap();
            render_ir_atomic_monadic(&operands[0], ctx, w);
            write!(w, " ").unwrap();
            render_ir_atomic_monadic(&operands[1], ctx, w);
            write!(w, " ").unwrap();
            render_ir_atomic_monadic(&operands[2], ctx, w);
        }
    }
}

/// Make a binding pattern from variable names.
pub fn make_pattern<S: AsRef<str>>(names: &[S]) -> String {
    super::render_tuple_like(names, "_", ", ", |name| {
        let name = name.as_ref();
        if name == "()" {
            "_".to_string()
        } else {
            escape::escape_identifier(name)
        }
    })
}

/// Render an IR node to a string.
pub fn ir_to_string(ir: &IRNode, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_ir(ir, ctx, &mut s);
    s
}

/// Render an IR node to a string, wrapping in parens if not atomic.
pub fn ir_to_string_atomic(ir: &IRNode, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_ir_atomic(ir, ctx, &mut s);
    s
}

/// Render an IR node to a string, adding ← prefix if monadic.
pub fn ir_to_string_maybe_monadic(ir: &IRNode, ctx: &RenderCtx) -> String {
    let mut s = String::new();
    render_ir_maybe_monadic(ir, ctx, &mut s);
    s
}

/// Render an IR node that may need monadic wrapping.
fn render_ir_maybe_monadic<W: Write>(ir: &IRNode, ctx: &RenderCtx, w: &mut W) {
    if !ctx.current_function_monadic {
        render_ir(ir, ctx, w);
    } else if is_call_monadic(ir, ctx) {
        write!(w, "← ").unwrap();
        render_ir_atomic(ir, ctx, w);
    } else {
        render_ir(ir, ctx, w);
    }
}

/// Render an IR node, wrapping in parens if not atomic.
fn render_ir_atomic<W: Write>(ir: &IRNode, ctx: &RenderCtx, w: &mut W) {
    if ir.is_atomic() {
        render_ir(ir, ctx, w);
    } else {
        write!(w, "(").unwrap();
        render_ir(ir, ctx, w);
        write!(w, ")").unwrap();
    }
}

/// Render an IR node, wrapping in parens if not atomic, and adding ← if monadic.
fn render_ir_atomic_monadic<W: Write>(ir: &IRNode, ctx: &RenderCtx, w: &mut W) {
    if !ctx.current_function_monadic {
        render_ir_atomic(ir, ctx, w);
    } else if is_call_monadic(ir, ctx) {
        write!(w, "(← ").unwrap();
        render_ir(ir, ctx, w);
        write!(w, ")").unwrap();
    } else {
        render_ir_atomic(ir, ctx, w);
    }
}
