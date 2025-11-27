// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Expression IR to Lean syntax.
//! Pure translation - pattern match IR nodes to Lean text.

use std::fmt::Write;
use intermediate_theorem_format::{
    Expression, BinOp, UnOp, VectorOp, ConstantValue, TempId,
    VariableRegistry, TheoremProgram, TheoremModuleID, Block, Statement,
};
use super::type_renderer::{render_type, uint_type_name, uint_cast_func};
use super::statement_renderer::render_stmt;
use super::lean_writer::LeanWriter;
use crate::escape;

/// Rendering context - holds references needed during rendering.
pub struct RenderCtx<'a> {
    pub registry: &'a VariableRegistry,
    pub program: &'a TheoremProgram,
    pub current_module_id: TheoremModuleID,
    pub current_module_namespace: Option<&'a str>,
}

/// Render an expression to Lean syntax.
pub fn render_expr<W: Write>(expr: &Expression, ctx: &RenderCtx, w: &mut W) {
    match expr {
        Expression::Temporary(temp_id) => {
            write!(w, "{}", ctx.registry.get_display_name(*temp_id)).unwrap();
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
                write!(w, "(").unwrap();
                render_expr(value, ctx, w);
                write!(w, ".{})", uint_cast_func(*bits as usize)).unwrap();
            } else {
                write!(w, "(cast ").unwrap();
                render_expr(value, ctx, w);
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

            let has_args = !type_args.is_empty() || !args.is_empty();
            if has_args {
                write!(w, "({}", func_name).unwrap();
                for ty in type_args {
                    write!(w, " ").unwrap();
                    render_type(ty, &ctx.program.name_manager, ctx.current_module_namespace, w);
                }
                for arg in args {
                    write!(w, " ").unwrap();
                    render_expr(arg, ctx, w);
                }
                write!(w, ")").unwrap();
            } else {
                write!(w, "{}", func_name).unwrap();
            }
        }

        Expression::Pack { struct_id, type_args, fields } => {
            let struct_def = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct definition for ID: {}", struct_id));
            let struct_name = escape::escape_struct_name(&struct_def.name);

            write!(w, "({}.mk", struct_name).unwrap();
            // Render type arguments for generic structs
            for ty in type_args {
                write!(w, " ").unwrap();
                render_type(ty, &ctx.program.name_manager, ctx.current_module_namespace, w);
            }
            for field in fields {
                write!(w, " ").unwrap();
                render_expr(field, ctx, w);
            }
            write!(w, ")").unwrap();
        }

        Expression::FieldAccess { struct_id, field_index, operand } => {
            let struct_def = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct definition for ID: {}", struct_id));
            let struct_name = escape::escape_struct_name(&struct_def.name);
            let field = &struct_def.fields[*field_index];
            let field_name = escape::escape_identifier(&field.name);

            write!(w, "({}.{} ", struct_name, field_name).unwrap();
            render_expr(operand, ctx, w);
            write!(w, ")").unwrap();
        }

        Expression::Unpack { struct_id, operand } => {
            let struct_def = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct definition for ID: {}", struct_id));
            let struct_name = escape::escape_struct_name(&struct_def.name);

            write!(w, "(").unwrap();
            for (i, field) in struct_def.fields.iter().enumerate() {
                if i > 0 {
                    write!(w, ", ").unwrap();
                }
                write!(w, "({}.{} ", struct_name, escape::escape_identifier(&field.name)).unwrap();
                render_expr(operand, ctx, w);
                write!(w, ")").unwrap();
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

        Expression::IfExpr { condition, then_block, else_block } => {
            // Inline if expression: (if cond then block else block)
            // Both branches must have the same type, so if either is monadic, both must be
            let either_monadic = then_block.is_monadic() || then_block.result.is_monadic()
                || else_block.is_monadic() || else_block.result.is_monadic();

            write!(w, "(if ").unwrap();
            render_expr(condition, ctx, w);
            write!(w, " then ").unwrap();
            render_block_inline_with_context(then_block, either_monadic, ctx, w);
            write!(w, " else ").unwrap();
            render_block_inline_with_context(else_block, either_monadic, ctx, w);
            write!(w, ")").unwrap();
        }

        Expression::WhileExpr { condition, body, state } => {
            // Inline while: (whileLoop (fun s => cond_block) (fun s => body_block) init)
            let state_pattern = make_pattern(&state.vars, ctx.registry);

            let mut init_str = String::new();
            render_tuple_or_single(&state.initial, ctx, &mut init_str);

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
    let need_monadic = block.is_monadic() || block.result.is_monadic();
    render_block_inline_with_context(block, need_monadic, ctx, w);
}

/// Render a block inline with explicit monadic context.
/// When `need_monadic` is true, renders using `do` notation.
/// When false, renders using `Id.run do` for pure blocks.
fn render_block_inline_with_context<W: Write>(block: &Block, need_monadic: bool, ctx: &RenderCtx, w: &mut W) {
    let block_is_monadic = block.is_monadic() || block.result.is_monadic();

    if block.statements.is_empty() {
        // No statements - just render result
        if block_is_monadic {
            render_expr(&block.result, ctx, w);
        } else if need_monadic {
            // Need to lift pure result into monad
            write!(w, "pure ").unwrap();
            render_expr(&block.result, ctx, w);
        } else {
            // Pure context, pure result - use Id.run
            write!(w, "(Id.run do pure ").unwrap();
            render_expr(&block.result, ctx, w);
            write!(w, ")").unwrap();
        }
    } else if need_monadic || block_is_monadic {
        // Monadic block - use do notation
        write!(w, "(do ").unwrap();

        // Use inline writer for statements
        let mut inline_writer = LeanWriter::new_inline(String::new());
        for stmt in &block.statements {
            render_stmt(stmt, ctx, &mut inline_writer);
            inline_writer.write("\n"); // becomes "; " in inline mode
        }
        write!(w, "{}", inline_writer.into_inner()).unwrap();

        if block.result.is_monadic() {
            render_expr(&block.result, ctx, w);
        } else {
            write!(w, "pure ").unwrap();
            render_expr(&block.result, ctx, w);
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
        if let Statement::Let { results, operation, .. } = stmt {
            let pattern = make_pattern(results, ctx.registry);
            write!(w, "let {} := ", pattern).unwrap();
            render_expr(operation, ctx, w);
            write!(w, "; ").unwrap();
        }
        // Skip non-Let statements in pure context (shouldn't happen)
    }
    write!(w, "pure ").unwrap();
    render_expr(&block.result, ctx, w);
}

/// Render a constant value.
fn render_constant<W: Write>(value: &ConstantValue, w: &mut W) {
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
                render_constant(e, w);
            }
            write!(w, "]").unwrap();
        }
    }
}

/// Render a binary operation.
fn render_binop<W: Write>(op: BinOp, lhs: &Expression, rhs: &Expression, ctx: &RenderCtx, w: &mut W) {
    let (prefix, infix, suffix) = match op {
        BinOp::Add => ("(", " + ", ")"),
        BinOp::Sub => ("(", " - ", ")"),
        BinOp::Mul => ("(", " * ", ")"),
        BinOp::Div => ("(", " / ", ")"),
        BinOp::Mod => ("(", " % ", ")"),
        BinOp::BitAnd => ("(", " &&& ", ")"),
        BinOp::BitOr => ("(", " ||| ", ")"),
        BinOp::BitXor => ("(", " ^^^ ", ")"),
        BinOp::Shl => ("(", " <<< ", ")"),
        BinOp::Shr => ("(", " >>> ", ")"),
        BinOp::And => ("(", " && ", ")"),
        BinOp::Or => ("(", " || ", ")"),
        BinOp::Eq => ("(", " == ", ")"),
        BinOp::Neq => ("(", " != ", ")"),
        BinOp::Lt => ("(decide (", " < ", "))"),
        BinOp::Le => ("(decide (", " ≤ ", "))"),
        BinOp::Gt => ("(decide (", " > ", "))"),
        BinOp::Ge => ("(decide (", " ≥ ", "))"),
    };

    write!(w, "{}", prefix).unwrap();
    render_expr(lhs, ctx, w);
    write!(w, "{}", infix).unwrap();
    render_expr(rhs, ctx, w);
    write!(w, "{}", suffix).unwrap();
}

/// Render a unary operation.
fn render_unop<W: Write>(op: UnOp, operand: &Expression, ctx: &RenderCtx, w: &mut W) {
    match op {
        UnOp::Not => {
            write!(w, "(!").unwrap();
            render_expr(operand, ctx, w);
            write!(w, ")").unwrap();
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
            write!(w, "({} ", uint_cast_func(bits)).unwrap();
            render_expr(operand, ctx, w);
            write!(w, ")").unwrap();
        }
    }
}

/// Render a vector operation.
fn render_vec_op<W: Write>(op: VectorOp, operands: &[Expression], ctx: &RenderCtx, w: &mut W) {
    match op {
        VectorOp::Empty => write!(w, "List.nil").unwrap(),
        VectorOp::Length => {
            write!(w, "(List.length ").unwrap();
            render_expr(&operands[0], ctx, w);
            write!(w, ")").unwrap();
        }
        VectorOp::Push => {
            write!(w, "(List.concat ").unwrap();
            render_expr(&operands[0], ctx, w);
            write!(w, " [").unwrap();
            render_expr(&operands[1], ctx, w);
            write!(w, "])").unwrap();
        }
        VectorOp::Pop => {
            write!(w, "(List.dropLast ").unwrap();
            render_expr(&operands[0], ctx, w);
            write!(w, ")").unwrap();
        }
        VectorOp::Borrow | VectorOp::BorrowMut => {
            write!(w, "(List.get! ").unwrap();
            render_expr(&operands[0], ctx, w);
            write!(w, " ").unwrap();
            render_expr(&operands[1], ctx, w);
            write!(w, ")").unwrap();
        }
        VectorOp::Swap => {
            write!(w, "(List.swap ").unwrap();
            render_expr(&operands[0], ctx, w);
            write!(w, " ").unwrap();
            render_expr(&operands[1], ctx, w);
            write!(w, " ").unwrap();
            render_expr(&operands[2], ctx, w);
            write!(w, ")").unwrap();
        }
    }
}

/// Make a binding pattern from temp IDs.
pub fn make_pattern(temps: &[TempId], registry: &VariableRegistry) -> String {
    if temps.is_empty() {
        "_".to_string()
    } else if temps.len() == 1 {
        let name = registry.get_display_name(temps[0]);
        if name == "()" { "_".to_string() } else { name }
    } else {
        let names: Vec<_> = temps.iter()
            .map(|t| {
                let name = registry.get_display_name(*t);
                if name == "()" { "_".to_string() } else { name }
            })
            .collect();
        format!("({})", names.join(", "))
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
