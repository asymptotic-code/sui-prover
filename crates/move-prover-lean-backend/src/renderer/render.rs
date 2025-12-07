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
            ctx.tuple(elems.iter(), "()", |ctx, elem| render(elem, ctx));
        }

        IRNode::BinOp { op, lhs, rhs } => {
            render_with_parens_if_needed(lhs, ctx);
            ctx.write(binop_symbol(*op));
            render_with_parens_if_needed(rhs, ctx);
        }

        IRNode::UnOp { op, operand } => {
            match op {
                UnOp::Not => {
                    // Use ¬ (Not) for Props instead of ! (which is for Bool)
                    ctx.write("¬");
                    render_with_parens_if_needed(operand, ctx);
                }
                cast => {
                    render_with_parens_if_needed(operand, ctx);
                    ctx.write(&format!(".{}", cast_func_name(cast)));
                }
            }
        }

        IRNode::Call {
            function,
            args,
            type_args,
        } => {
            let func = ctx.program.functions.get(function);
            let func_name = if func.module_id == ctx.current_module_id {
                escape::escape_identifier(&func.full_name(function.variant))
            } else {
                let module = ctx.program.modules.get(func.module_id);
                let namespace = escape::module_name_to_namespace(&module.name);
                format!(
                    "{}.{}",
                    namespace,
                    escape::escape_identifier(&func.full_name(function.variant))
                )
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

        IRNode::Pack {
            struct_id,
            type_args,
            fields,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            ctx.write(&format!(
                "{}.mk",
                escape::escape_struct_name(&struct_def.name)
            ));
            for ty in type_args {
                ctx.write(" ");
                render_type(ty, ctx);
            }
            for field in fields {
                ctx.write(" ");
                render_with_parens_if_needed(field, ctx);
            }
        }

        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let field_name = &struct_def.fields[*field_index].name;
            ctx.write(&format!(
                "{}.{} ",
                escape::escape_struct_name(&struct_def.name),
                escape::escape_identifier(field_name)
            ));
            render_with_parens_if_needed(base, ctx);
        }

        IRNode::Unpack { struct_id, value } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);
            ctx.write("(");
            ctx.sep_with(", ", struct_def.fields.iter(), |ctx, field| {
                ctx.write(&struct_name);
                ctx.write(".");
                ctx.write(&escape::escape_identifier(&field.name));
                ctx.write(" ");
                render_with_parens_if_needed(value, ctx);
            });
            ctx.write(")");
        }

        IRNode::VecOp { op, args } => match op {
            VecOp::Empty(_) => ctx.write("List.nil"),
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
        },

        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => {
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
            ctx.write("let ");
            ctx.tuple(
                pattern.iter(),
                "_",
                |ctx, p| ctx.write(&escape::escape_identifier(p)),
            );
            ctx.write(" := ");
            render(value, ctx);
        }

        IRNode::Block { children } => {
            for (i, child) in children.iter().enumerate() {
                let is_last = i == children.len() - 1;
                render(child, ctx);
                if !is_last {
                    ctx.newline();
                }
            }
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            ctx.write("if ");
            render(cond, ctx);
            ctx.write(" then");
            ctx.indent(true);
            render(then_branch, ctx);
            ctx.dedent(false);
            ctx.newline();
            ctx.write("else");
            ctx.indent(true);
            render(else_branch, ctx);
            ctx.dedent(false);
        }

        IRNode::While { cond, body, vars } => {
            let vars_str = vars.join(", ");
            ctx.write(&format!("whileLoopPure (fun ({}) =>", vars_str));
            ctx.indent(true);
            render(cond, ctx);
            ctx.dedent(false);
            ctx.newline();
            ctx.write(&format!(") (fun ({}) =>", vars_str));
            ctx.indent(true);
            render(body, ctx);
            ctx.newline();
            ctx.write(&format!("({})", vars_str));
            ctx.dedent(false);
            ctx.newline();
            ctx.write(&format!(") ({})", vars_str));
        }

        IRNode::Return(values) => {
            ctx.tuple(values.iter(), "()", |ctx, v| render(v, ctx));
        }

        IRNode::Abort(_) => {
            // Abort nodes should not appear in pure code - they are filtered out
            // during the Pure variant generation. If we hit this, something is wrong.
            panic!("BUG: Abort node encountered in pure rendering context");
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

fn render_const<W: Write>(c: &Const, ctx: &mut RenderCtx<W>) {
    match c {
        Const::Bool(b) => ctx.write(if *b { "True" } else { "False" }),
        Const::UInt { bits, value } => {
            if *bits == 8 || *bits == 128 {
                ctx.write(&format!("({} : {})", value, uint_type_name(*bits)));
            } else {
                ctx.write(&value.to_string());
            }
        }
        Const::Address(addr) => ctx.write(&addr.to_string()),
        Const::Vector { elems, .. } => {
            ctx.write("[");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    ctx.write(", ");
                }
                render_const(e, ctx);
            }
            ctx.write("]");
        }
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
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
    }
}

fn cast_func_name(op: &UnOp) -> &'static str {
    match op {
        UnOp::CastU8 => "toUInt8",
        UnOp::CastU16 => "toUInt16",
        UnOp::CastU32 => "toUInt32",
        UnOp::CastU64 => "toUInt64",
        UnOp::CastU128 => "toUInt128",
        UnOp::CastU256 => "toUInt256",
        _ => panic!("Not a cast: {:?}", op),
    }
}

fn uint_type_name(bits: usize) -> &'static str {
    match bits {
        8 => "UInt8",
        16 => "UInt16",
        32 => "UInt32",
        64 => "UInt64",
        128 => "UInt128",
        256 => "UInt256",
        _ => panic!("Invalid uint size: {}", bits),
    }
}
