// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Expression rendering - writes IR nodes directly to the context

use super::context::RenderCtx;
use super::type_renderer::render_type;
use crate::escape;
use intermediate_theorem_format::{BinOp, Const, IRNode, UnOp, VecOp};
use std::fmt::Write;

/// Render an IR expression node directly to the context
pub fn render<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    match ir {
        IRNode::Var(name) => ctx.write(&escape::escape_identifier(name)),
        IRNode::Const(c) => render_const(c, false, ctx),
        IRNode::BinOp { op, lhs, rhs } => render_binop(*op, lhs, rhs, ctx),
        IRNode::UnOp { op, operand } => render_unop(*op, operand, ctx),
        IRNode::Call { function, args, type_args } => render_call(*function, type_args, args, ctx),
        IRNode::Pack { struct_id, type_args, fields } => render_pack(*struct_id, type_args, fields, ctx),
        IRNode::Field { struct_id, field_index, base } => render_field(*struct_id, *field_index, base, ctx),
        IRNode::Unpack { struct_id, value } => render_unpack(*struct_id, value, ctx),
        IRNode::VecOp { op, args } => render_vec_op(*op, args, ctx),
        IRNode::Tuple(elems) => render_tuple(elems, ctx),
        IRNode::UpdateField { base, struct_id, field_index, value } => {
            ctx.write("{ ");
            render(base, ctx);
            let field_name = &ctx.program.structs.get(*struct_id).fields[*field_index].name;
            ctx.write(&format!(" with {} := ", field_name));
            render(value, ctx);
            ctx.write(" }");
        }
        IRNode::UpdateVec { base, index, value } => {
            render(base, ctx);
            ctx.write(".set ");
            render_parens(index, ctx);
            ctx.write(" ");
            render_parens(value, ctx);
        }
        IRNode::Abort(code) => {
            ctx.write("Except.error ");
            render_parens(code, ctx);
        }
        IRNode::Let { pattern, value, .. } => {
            // In expression position, render as inline let
            let pattern_str: Vec<_> = pattern.iter().map(|p| escape::escape_identifier(p)).collect();
            let is_monadic = value.is_monadic(&|fid| ctx.is_func_monadic(fid));
            ctx.write("let ");
            ctx.write(&pattern_str.join(", "));
            ctx.write(if is_monadic { " ← " } else { " := " });
            render(value, ctx);
        }
        IRNode::Return(values) => {
            if values.is_empty() {
                ctx.write("()");
            } else if values.len() == 1 {
                render(&values[0], ctx);
            } else {
                ctx.write("(");
                for (i, v) in values.iter().enumerate() {
                    if i > 0 { ctx.write(", "); }
                    render(v, ctx);
                }
                ctx.write(")");
            }
        }
        IRNode::Requires(cond) | IRNode::Ensures(cond) => {
            ctx.write("-- spec: ");
            render(cond, ctx);
        }
        // Blocks in expression position - inline rendering
        IRNode::Block { children } => {
            if children.is_empty() {
                ctx.write("()");
                return;
            }

            // Get statements and result
            let stmts = &children[..children.len().saturating_sub(1)];
            let result = children.last().unwrap();

            if stmts.is_empty() {
                // No statements, just render the result
                render(result, ctx);
            } else {
                // Has statements - check if any are monadic
                let has_monadic = stmts.iter().any(|s| s.contains_monadic(&|fid| ctx.is_func_monadic(fid)))
                    || result.contains_monadic(&|fid| ctx.is_func_monadic(fid));

                if has_monadic {
                    // Monadic block - use plain do
                    ctx.write("(do");
                    for stmt in stmts {
                        ctx.write(" ");
                        render(stmt, ctx);
                        ctx.write(";");
                    }
                    ctx.write(" ");
                    // Check if result itself is monadic - if not, wrap in pure
                    if result.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
                        render(result, ctx);
                    } else {
                        ctx.write("pure ");
                        render(result, ctx);
                    }
                    ctx.write(")");
                } else {
                    // Pure block - check for simple let pattern
                    // If we have: let x := val; x, we can simplify to just val
                    if stmts.len() == 1 {
                        if let IRNode::Let { pattern, value } = &stmts[0] {
                            if pattern.len() == 1 {
                                if let IRNode::Var(result_var) = result {
                                    if &pattern[0] == result_var {
                                        // Simple case: let x := val; x -> just render val
                                        render(value, ctx);
                                        return;
                                    }
                                }
                            }
                        }
                    }

                    // General case - use Id.run do
                    ctx.write("(Id.run do");
                    for stmt in stmts {
                        ctx.write(" ");
                        render(stmt, ctx);
                        ctx.write(";");
                    }
                    ctx.write(" ");
                    render(result, ctx);
                    ctx.write(")");
                }
            }
        }
        IRNode::If { cond, then_branch, else_branch } => {
            // Check if any part is monadic
            let cond_monadic = cond.contains_monadic(&|fid| ctx.is_func_monadic(fid));
            let branches_monadic = then_branch.contains_monadic(&|fid| ctx.is_func_monadic(fid))
                || else_branch.contains_monadic(&|fid| ctx.is_func_monadic(fid));

            if cond_monadic || branches_monadic {
                // Cannot render monadic if inline - wrap in do block
                ctx.write("(do ");
                if cond_monadic {
                    // Bind condition first
                    ctx.write("let __cond ← ");
                    render(cond, ctx);
                    ctx.write("; if __cond then (");
                } else {
                    ctx.write("if ");
                    render(cond, ctx);
                    ctx.write(" then (");
                }
                render(then_branch, ctx);
                ctx.write(") else (");
                render(else_branch, ctx);
                ctx.write("))");
            } else {
                ctx.write("if ");
                render(cond, ctx);
                ctx.write(" then ");
                render(then_branch, ctx);
                ctx.write(" else ");
                render(else_branch, ctx);
            }
        }
        IRNode::While { .. } => {
            // While loops in expression position need special handling
            ctx.write("(sorry -- while in expr position)");
        }
    }
}

/// Render with parentheses if needed
#[inline]
pub fn render_parens<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    if ir.is_atomic() {
        render(ir, ctx);
    } else {
        ctx.write("(");
        render(ir, ctx);
        ctx.write(")");
    }
}

/// Render with monadic arrow if needed
#[inline]
pub fn render_with_arrow<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    if ir.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
        ctx.write("← ");
        render_parens(ir, ctx);
    } else {
        render(ir, ctx);
    }
}

/// Render as argument (with monadic wrapping and parens)
#[inline]
fn render_arg<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    if ir.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
        ctx.write("(← ");
        render(ir, ctx);
        ctx.write(")");
    } else {
        render_parens(ir, ctx);
    }
}

fn render_const<W: Write>(c: &Const, force_type: bool, ctx: &mut RenderCtx<W>) {
    match c {
        Const::Bool(b) => ctx.write(if *b { "true" } else { "false" }),
        Const::UInt { bits, value: v } => {
            if force_type || *bits == 8 || *bits == 128 {
                ctx.write(&format!("({} : {})", v, uint_type_name(*bits)));
            } else {
                ctx.write(&v.to_string());
            }
        }
        Const::Address(addr) => ctx.write(&addr.to_string()),
        Const::Vector(elems) => {
            ctx.write("[");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 { ctx.write(", "); }
                render_const(e, force_type, ctx);
            }
            ctx.write("]");
        }
    }
}

fn render_binop<W: Write>(op: BinOp, lhs: &IRNode, rhs: &IRNode, ctx: &mut RenderCtx<W>) {
    let is_comparison = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
    let is_shift = matches!(op, BinOp::Shl | BinOp::Shr);

    if is_comparison { ctx.write("decide ("); }

    if is_shift {
        match lhs {
            IRNode::Const(c) => render_const(c, true, ctx),
            _ => render_arg(lhs, ctx),
        }
    } else {
        render_arg(lhs, ctx);
    }

    ctx.write(match op {
        BinOp::Add => " + ", BinOp::Sub => " - ", BinOp::Mul => " * ", BinOp::Div => " / ", BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ", BinOp::BitOr => " ||| ", BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ", BinOp::Shr => " >>> ",
        BinOp::And => " && ", BinOp::Or => " || ",
        BinOp::Eq => " == ", BinOp::Neq => " != ",
        BinOp::Lt => " < ", BinOp::Le => " ≤ ", BinOp::Gt => " > ", BinOp::Ge => " ≥ ",
    });

    if is_shift {
        match rhs {
            IRNode::Const(c) => render_const(c, true, ctx),
            _ => render_parens(rhs, ctx),
        }
    } else {
        render_arg(rhs, ctx);
    }

    if is_comparison { ctx.write(")"); }
}

fn render_unop<W: Write>(op: UnOp, operand: &IRNode, ctx: &mut RenderCtx<W>) {
    match op {
        UnOp::Not => {
            ctx.write("!");
            render_arg(operand, ctx);
        }
        cast => {
            render_arg(operand, ctx);
            let bits = match cast {
                UnOp::CastU8 => 8, UnOp::CastU16 => 16, UnOp::CastU32 => 32,
                UnOp::CastU64 => 64, UnOp::CastU128 => 128, UnOp::CastU256 => 256,
                _ => unreachable!(),
            };
            ctx.write(&format!(".{}", uint_cast_func(bits)));
        }
    }
}

fn render_call<W: Write>(
    function: intermediate_theorem_format::FunctionID,
    type_args: &[intermediate_theorem_format::Type],
    args: &[IRNode],
    ctx: &mut RenderCtx<W>,
) {
    let func = ctx.program.functions.get(function);
    let func_name = if func.module_id == ctx.current_module_id {
        escape::escape_identifier(&func.name)
    } else {
        let module = ctx.program.modules.get(func.module_id);
        let namespace = escape::module_name_to_namespace(&module.name);
        format!("{}.{}", namespace, escape::escape_identifier(&func.name))
    };

    ctx.write(&func_name);
    for ty in type_args {
        ctx.write(" ");
        let mut s = String::new();
        render_type(ty, ctx.program, ctx.current_module_namespace, &mut s);
        ctx.write(&s);
    }
    for arg in args {
        ctx.write(" ");
        render_arg(arg, ctx);
    }
}

fn render_pack<W: Write>(
    struct_id: intermediate_theorem_format::StructID,
    type_args: &[intermediate_theorem_format::Type],
    fields: &[IRNode],
    ctx: &mut RenderCtx<W>,
) {
    let struct_def = ctx.program.structs.get(struct_id);
    ctx.write(&format!("{}.mk", escape::escape_struct_name(&struct_def.name)));
    for ty in type_args {
        ctx.write(" ");
        let mut s = String::new();
        render_type(ty, ctx.program, ctx.current_module_namespace, &mut s);
        ctx.write(&s);
    }
    for field in fields {
        ctx.write(" ");
        render_arg(field, ctx);
    }
}

fn render_field<W: Write>(
    struct_id: intermediate_theorem_format::StructID,
    field_index: usize,
    base: &IRNode,
    ctx: &mut RenderCtx<W>,
) {
    let struct_def = ctx.program.structs.get(struct_id);
    let field_name = &struct_def.fields[field_index].name;
    ctx.write(&format!("{}.{} ",
        escape::escape_struct_name(&struct_def.name),
        escape::escape_identifier(field_name)));
    render_arg(base, ctx);
}

fn render_unpack<W: Write>(
    struct_id: intermediate_theorem_format::StructID,
    value: &IRNode,
    ctx: &mut RenderCtx<W>,
) {
    let struct_def = ctx.program.structs.get(struct_id);
    let struct_name = escape::escape_struct_name(&struct_def.name);
    ctx.write("(");
    for (i, field) in struct_def.fields.iter().enumerate() {
        if i > 0 { ctx.write(", "); }
        ctx.write(&format!("{}.{} ", struct_name, escape::escape_identifier(&field.name)));
        render_arg(value, ctx);
    }
    ctx.write(")");
}

fn render_vec_op<W: Write>(op: VecOp, args: &[IRNode], ctx: &mut RenderCtx<W>) {
    match op {
        VecOp::Empty => ctx.write("List.nil"),
        VecOp::Length => {
            ctx.write("List.length ");
            render_arg(&args[0], ctx);
        }
        VecOp::Push => {
            ctx.write("List.concat ");
            render_arg(&args[0], ctx);
            ctx.write(" [");
            render(&args[1], ctx);
            ctx.write("]");
        }
        VecOp::Pop => {
            ctx.write("List.dropLast ");
            render_arg(&args[0], ctx);
        }
        VecOp::Borrow | VecOp::BorrowMut => {
            ctx.write("List.get! ");
            render_arg(&args[0], ctx);
            ctx.write(" ");
            render_arg(&args[1], ctx);
        }
        VecOp::Swap => {
            ctx.write("List.swap ");
            render_arg(&args[0], ctx);
            ctx.write(" ");
            render_arg(&args[1], ctx);
            ctx.write(" ");
            render_arg(&args[2], ctx);
        }
    }
}

fn render_tuple<W: Write>(elems: &[IRNode], ctx: &mut RenderCtx<W>) {
    if elems.is_empty() {
        ctx.write("()");
        return;
    }

    if elems.len() == 1 {
        render_with_arrow(&elems[0], ctx);
        return;
    }

    let has_monadic = elems.iter().any(|e| e.is_monadic(&|fid| ctx.is_func_monadic(fid)));
    if !has_monadic {
        render_tuple_like_inline(elems, "(", ", ", render, ctx);
        ctx.write(")");
        return;
    }

    // Monadic tuple - sequence operations
    ctx.write("(do ");
    let mut temp_idx = 0;
    for (i, e) in elems.iter().enumerate() {
        if e.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
            ctx.write(&format!("let __t{} ← ", temp_idx));
            render(e, ctx);
            ctx.write("; ");
            temp_idx += 1;
        }
    }
    ctx.write("pure (");
    temp_idx = 0;
    for (i, e) in elems.iter().enumerate() {
        if i > 0 { ctx.write(", "); }
        if e.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
            ctx.write(&format!("__t{}", temp_idx));
            temp_idx += 1;
        } else {
            render(e, ctx);
        }
    }
    ctx.write("))");
}

/// Helper to render a tuple-like structure inline
fn render_tuple_like_inline<W: Write, F>(
    items: &[IRNode],
    prefix: &str,
    sep: &str,
    render_fn: F,
    ctx: &mut RenderCtx<W>,
) where
    F: Fn(&IRNode, &mut RenderCtx<W>),
{
    if items.is_empty() {
        ctx.write("()");
        return;
    }
    if items.len() == 1 {
        render_fn(&items[0], ctx);
        return;
    }
    ctx.write(prefix);
    for (i, item) in items.iter().enumerate() {
        if i > 0 { ctx.write(sep); }
        render_fn(item, ctx);
    }
}

// ============================================================================
// String-building helpers for stmt.rs
// ============================================================================

use super::lean_writer::LeanWriter;

/// Render expression to a string (for building complex format strings)
pub fn render_to_string<W: Write>(ir: &IRNode, ctx: &RenderCtx<W>) -> String {
    let mut s = String::new();
    let mut temp_ctx = RenderCtx::new(
        ctx.program,
        ctx.registry,
        ctx.current_module_id,
        ctx.current_module_namespace,
        LeanWriter::new(&mut s),
    );
    render(ir, &mut temp_ctx);
    s
}

/// Render expression with parentheses to a string
pub fn render_parens_to_string<W: Write>(ir: &IRNode, ctx: &RenderCtx<W>) -> String {
    let mut s = String::new();
    let mut temp_ctx = RenderCtx::new(
        ctx.program,
        ctx.registry,
        ctx.current_module_id,
        ctx.current_module_namespace,
        LeanWriter::new(&mut s),
    );
    render_parens(ir, &mut temp_ctx);
    s
}

/// Render expression with arrow to a string
pub fn render_with_arrow_to_string<W: Write>(ir: &IRNode, ctx: &RenderCtx<W>) -> String {
    let mut s = String::new();
    let mut temp_ctx = RenderCtx::new(
        ctx.program,
        ctx.registry,
        ctx.current_module_id,
        ctx.current_module_namespace,
        LeanWriter::new(&mut s),
    );
    render_with_arrow(ir, &mut temp_ctx);
    s
}

fn uint_type_name(bits: usize) -> &'static str {
    match bits {
        8 => "UInt8", 16 => "UInt16", 32 => "UInt32",
        64 => "UInt64", 128 => "UInt128", 256 => "UInt256",
        _ => panic!("Invalid uint size: {}", bits),
    }
}

fn uint_cast_func(bits: usize) -> &'static str {
    match bits {
        8 => "toUInt8", 16 => "toUInt16", 32 => "toUInt32",
        64 => "toUInt64", 128 => "toUInt128", 256 => "toUInt256",
        _ => panic!("Invalid uint size: {}", bits),
    }
}
