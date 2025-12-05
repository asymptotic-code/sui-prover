// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified IR renderer - renders IR nodes to Lean syntax

use super::context::RenderCtx;
use super::type_renderer::render_type;
use crate::escape;
use intermediate_theorem_format::{BinOp, Const, IRNode, UnOp, VecOp};
use std::fmt::Write;

/// Render an IR node to Lean syntax
pub fn render<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    match ir {
        // Atomic expressions - always inline
        IRNode::Var(name) => {
            ctx.write(&escape::escape_identifier(name));
        }

        IRNode::Const(c) => render_const(c, ctx),

        IRNode::Tuple(elems) => {
            if elems.is_empty() {
                ctx.write("()");
            } else if elems.len() == 1 {
                render(&elems[0], ctx);
            } else {
                ctx.write("(");
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 { ctx.write(", "); }
                    render(elem, ctx);
                }
                ctx.write(")");
            }
        }

        IRNode::BinOp { op, lhs, rhs } => {
            let is_comparison = matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge);
            if is_comparison { ctx.write("decide ("); }

            render_with_parens_if_needed(lhs, ctx);
            ctx.write(binop_symbol(*op));
            render_with_parens_if_needed(rhs, ctx);

            if is_comparison { ctx.write(")"); }
        }

        IRNode::UnOp { op, operand } => {
            match op {
                UnOp::Not => {
                    ctx.write("!");
                    render_with_parens_if_needed(operand, ctx);
                }
                cast => {
                    render_with_parens_if_needed(operand, ctx);
                    ctx.write(&format!(".{}", cast_func_name(cast)));
                }
            }
        }

        IRNode::Call { function, args, type_args } => {
            let func = ctx.program.functions.get(*function);
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
                render_type(ty, ctx);
            }
            for arg in args {
                ctx.write(" ");
                render_with_parens_if_needed(arg, ctx);
            }
        }

        IRNode::Pack { struct_id, type_args, fields } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            ctx.write(&format!("{}.mk", escape::escape_struct_name(&struct_def.name)));
            for ty in type_args {
                ctx.write(" ");
                render_type(ty, ctx);
            }
            for field in fields {
                ctx.write(" ");
                render_with_parens_if_needed(field, ctx);
            }
        }

        IRNode::Field { struct_id, field_index, base } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let field_name = &struct_def.fields[*field_index].name;
            ctx.write(&format!("{}.{} ",
                escape::escape_struct_name(&struct_def.name),
                escape::escape_identifier(field_name)));
            render_with_parens_if_needed(base, ctx);
        }

        IRNode::Unpack { struct_id, value } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);
            ctx.write("(");
            for (i, field) in struct_def.fields.iter().enumerate() {
                if i > 0 { ctx.write(", "); }
                ctx.write(&format!("{}.{} ", struct_name, escape::escape_identifier(&field.name)));
                render_with_parens_if_needed(value, ctx);
            }
            ctx.write(")");
        }

        IRNode::VecOp { op, args } => {
            match op {
                VecOp::Empty => ctx.write("List.nil"),
                VecOp::Length => {
                    ctx.write("List.length ");
                    render_with_parens_if_needed(&args[0], ctx);
                }
                VecOp::Push => {
                    ctx.write("List.concat ");
                    render_with_parens_if_needed(&args[0], ctx);
                    ctx.write(" [");
                    render(&args[1], ctx);
                    ctx.write("]");
                }
                VecOp::Pop => {
                    ctx.write("List.dropLast ");
                    render_with_parens_if_needed(&args[0], ctx);
                }
                VecOp::Borrow | VecOp::BorrowMut => {
                    ctx.write("List.get! ");
                    render_with_parens_if_needed(&args[0], ctx);
                    ctx.write(" ");
                    render_with_parens_if_needed(&args[1], ctx);
                }
                VecOp::Swap => {
                    ctx.write("List.swap ");
                    render_with_parens_if_needed(&args[0], ctx);
                    ctx.write(" ");
                    render_with_parens_if_needed(&args[1], ctx);
                    ctx.write(" ");
                    render_with_parens_if_needed(&args[2], ctx);
                }
            }
        }

        IRNode::UpdateField { base, struct_id, field_index, value } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let field_name = &struct_def.fields[*field_index].name;
            ctx.write("{ ");
            render(base, ctx);
            ctx.write(&format!(" with {} := ", field_name));
            render(value, ctx);
            ctx.write(" }");
        }

        IRNode::UpdateVec { base, index, value } => {
            render(base, ctx);
            ctx.write(".set ");
            render_with_parens_if_needed(index, ctx);
            ctx.write(" ");
            render_with_parens_if_needed(value, ctx);
        }

        // Non-atomic expressions - multi-line
        IRNode::Let { pattern, value } => {
            let pattern_str: Vec<_> = pattern.iter().map(|p| escape::escape_identifier(p)).collect();
            let is_monadic = value.is_monadic(&|fid| ctx.is_func_monadic(fid));
            ctx.write("let ");
            if pattern.len() > 1 {
                ctx.write("(");
                ctx.write(&pattern_str.join(", "));
                ctx.write(")");
            } else {
                ctx.write(&pattern_str.join(", "));
            }
            ctx.write(if is_monadic { " ← " } else { " := " });
            render(value, ctx);
        }

        IRNode::Block { children } => {
            if children.is_empty() {
                ctx.write("()");
                return;
            }

            // Check if block is monadic
            let is_monadic = children.iter().any(|c| c.contains_monadic(&|fid| ctx.is_func_monadic(fid)));

            if is_monadic {
                ctx.write("do\n");
                ctx.indent();
            }

            for (i, child) in children.iter().enumerate() {
                render(child, ctx);
                if i < children.len() - 1 {
                    ctx.newline();
                }
            }

            if is_monadic {
                ctx.dedent();
            }
        }

        IRNode::If { cond, then_branch, else_branch } => {
            ctx.write("if ");
            render(cond, ctx);
            ctx.write(" then\n");
            ctx.indent();
            render_as_single_expr(then_branch, ctx);
            ctx.dedent();
            ctx.write("\nelse\n");
            ctx.indent();
            render_as_single_expr(else_branch, ctx);
            ctx.dedent();
        }

        IRNode::While { cond, body, vars } => {
            ctx.write(&format!("whileLoop (fun ({}) =>\n", vars.join(", ")));
            ctx.indent();

            // Render condition
            render(cond, ctx);

            ctx.dedent();
            ctx.write(&format!(") (fun ({}) =>\n", vars.join(", ")));
            ctx.indent();

            // Render body
            render(body, ctx);

            // Add return tuple for loop variables
            ctx.newline();
            ctx.write(&format!("({})", vars.join(", ")));

            ctx.dedent();
            ctx.write(&format!(") ({})", vars.join(", ")));
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

        IRNode::Abort(code) => {
            ctx.write("Except.error ");
            render_with_parens_if_needed(code, ctx);
        }

        IRNode::Requires(_) | IRNode::Ensures(_) => {
            // Spec nodes should be stripped before rendering
        }
    }
}

fn render_with_parens_if_needed<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    if ir.is_atomic() {
        render(ir, ctx);
    } else {
        ctx.write("(");
        render(ir, ctx);
        ctx.write(")");
    }
}

/// Render an IR node as a single expression suitable for if-then-else branches.
/// If the node is a Block with multiple statements, wrap it appropriately.
fn render_as_single_expr<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    match ir {
        IRNode::Block { children } if children.len() > 1 => {
            // Multiple statements - check if monadic
            let is_monadic = children.iter().any(|c| c.contains_monadic(&|fid| ctx.is_func_monadic(fid)));
            if is_monadic {
                ctx.write("do\n");
                ctx.indent();
                for (i, child) in children.iter().enumerate() {
                    render(child, ctx);
                    if i < children.len() - 1 {
                        ctx.newline();
                    }
                }
                ctx.dedent();
            } else {
                // Non-monadic block - render last child only
                // (earlier statements should have been optimized away)
                render(children.last().unwrap(), ctx);
            }
        }
        _ => render(ir, ctx),
    }
}

fn render_const<W: Write>(c: &Const, ctx: &mut RenderCtx<W>) {
    match c {
        Const::Bool(b) => ctx.write(if *b { "true" } else { "false" }),
        Const::UInt { bits, value } => {
            if *bits == 8 || *bits == 128 {
                ctx.write(&format!("({} : {})", value, uint_type_name(*bits)));
            } else {
                ctx.write(&value.to_string());
            }
        }
        Const::Address(addr) => ctx.write(&addr.to_string()),
        Const::Vector(elems) => {
            ctx.write("[");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 { ctx.write(", "); }
                render_const(e, ctx);
            }
            ctx.write("]");
        }
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => " + ", BinOp::Sub => " - ", BinOp::Mul => " * ",
        BinOp::Div => " / ", BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ", BinOp::BitOr => " ||| ", BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ", BinOp::Shr => " >>> ",
        BinOp::And => " && ", BinOp::Or => " || ",
        BinOp::Eq => " == ", BinOp::Neq => " != ",
        BinOp::Lt => " < ", BinOp::Le => " ≤ ", BinOp::Gt => " > ", BinOp::Ge => " ≥ ",
    }
}

fn cast_func_name(op: &UnOp) -> &'static str {
    match op {
        UnOp::CastU8 => "toUInt8", UnOp::CastU16 => "toUInt16", UnOp::CastU32 => "toUInt32",
        UnOp::CastU64 => "toUInt64", UnOp::CastU128 => "toUInt128", UnOp::CastU256 => "toUInt256",
        _ => panic!("Not a cast: {:?}", op),
    }
}

fn uint_type_name(bits: usize) -> &'static str {
    match bits {
        8 => "UInt8", 16 => "UInt16", 32 => "UInt32",
        64 => "UInt64", 128 => "UInt128", 256 => "UInt256",
        _ => panic!("Invalid uint size: {}", bits),
    }
}
