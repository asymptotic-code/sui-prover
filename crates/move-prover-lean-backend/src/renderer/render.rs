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
            let lhs_monadic = lhs.is_monadic(&|fid| ctx.is_func_monadic(fid));
            let rhs_monadic = rhs.is_monadic(&|fid| ctx.is_func_monadic(fid));

            if lhs_monadic || rhs_monadic {
                // Need to bind monadic operands first
                ctx.write("(do\n");
                ctx.indent();
                if lhs_monadic {
                    ctx.write("let __lhs ← ");
                    render(lhs, ctx);
                    ctx.newline();
                }
                if rhs_monadic {
                    ctx.write("let __rhs ← ");
                    render(rhs, ctx);
                    ctx.newline();
                }
                ctx.write("pure (");
                if is_comparison { ctx.write("decide ("); }
                if lhs_monadic {
                    ctx.write("__lhs");
                } else {
                    render_with_parens_if_needed(lhs, ctx);
                }
                ctx.write(binop_symbol(*op));
                if rhs_monadic {
                    ctx.write("__rhs");
                } else {
                    render_with_parens_if_needed(rhs, ctx);
                }
                if is_comparison { ctx.write(")"); }
                ctx.write("))");
                ctx.dedent();
            } else {
                if is_comparison { ctx.write("decide ("); }
                render_with_parens_if_needed(lhs, ctx);
                ctx.write(binop_symbol(*op));
                render_with_parens_if_needed(rhs, ctx);
                if is_comparison { ctx.write(")"); }
            }
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
                // Add <- prefix for monadic arguments (wrapped in parens)
                let arg_is_monadic = arg.is_monadic(&|fid| ctx.is_func_monadic(fid));
                if arg_is_monadic {
                    ctx.write("(<- ");
                    render_with_parens_if_needed(arg, ctx);
                    ctx.write(")");
                } else {
                    render_with_parens_if_needed(arg, ctx);
                }
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
            if pattern.is_empty() {
                ctx.write("_");
            } else if pattern.len() > 1 {
                ctx.write("(");
                ctx.write(&pattern_str.join(", "));
                ctx.write(")");
            } else {
                ctx.write(&pattern_str.join(", "));
            }

            // Always use :=, but add <- prefix to the value if it's monadic
            ctx.write(" := ");
            if is_monadic {
                ctx.write("<- ");
            }
            render(value, ctx);
        }

        IRNode::Block { children } => {
            if children.is_empty() {
                // Don't render anything for empty blocks
                return;
            }

            // Check if block is monadic
            let is_monadic = children.iter().any(|c| c.contains_monadic(&|fid| ctx.is_func_monadic(fid)));

            // Filter out spec nodes and empty blocks
            let filtered_children: Vec<&IRNode> = children.iter()
                .filter(|c| !matches!(c, IRNode::Requires(_) | IRNode::Ensures(_)))
                .filter(|c| !matches!(c, IRNode::Block { children } if children.is_empty()))
                .collect();

            if filtered_children.is_empty() {
                // All children were filtered out - don't render anything
                return;
            }

            if is_monadic {
                ctx.write("do\n");
                ctx.indent();
            }

            for (i, child) in filtered_children.iter().enumerate() {
                let is_last = i == filtered_children.len() - 1;

                if is_last && is_monadic {
                    // Last child in monadic block - wrap with pure if needed
                    render_monadic(child, ctx);
                } else if !is_last && is_monadic {
                    // Non-final child in monadic block
                    // If it's a monadic Call that's not a Let, bind it with let _ ←
                    if matches!(child, IRNode::Call { function: f, .. } if ctx.is_func_monadic(*f)) {
                        ctx.write("let _ ← ");
                    }
                    render(child, ctx);
                } else {
                    render(child, ctx);
                }
                if i < filtered_children.len() - 1 {
                    ctx.newline();
                }
            }

            if is_monadic {
                ctx.dedent();
            }
        }

        IRNode::If { cond, then_branch, else_branch } => {
            // Check if either branch is monadic
            let is_monadic = then_branch.is_monadic(&|fid| ctx.is_func_monadic(fid))
                || else_branch.is_monadic(&|fid| ctx.is_func_monadic(fid));

            // Check if condition is monadic
            let cond_is_monadic = cond.is_monadic(&|fid| ctx.is_func_monadic(fid));

            if cond_is_monadic {
                // Bind the monadic condition first, then use the bound value
                ctx.write("(do\n");
                ctx.indent();
                ctx.write("let __cond ← ");
                render(cond, ctx);
                ctx.newline();
                ctx.write("if __cond then\n");
                ctx.indent();
                render_as_single_expr(then_branch, ctx, true);
                ctx.dedent();
                ctx.write("\nelse\n");
                ctx.indent();
                render_as_single_expr(else_branch, ctx, true);
                ctx.dedent();
                ctx.write(")");
                ctx.dedent();
            } else {
                ctx.write("if ");
                render(cond, ctx);
                ctx.write(" then\n");
                ctx.indent();
                render_as_single_expr(then_branch, ctx, is_monadic);
                ctx.dedent();
                ctx.write("\nelse\n");
                ctx.indent();
                render_as_single_expr(else_branch, ctx, is_monadic);
                ctx.dedent();
            }
        }

        IRNode::While { cond, body, vars } => {
            // Check if loop is monadic
            let cond_is_monadic = cond.is_monadic(&|fid| ctx.is_func_monadic(fid));
            let body_is_monadic = body.is_monadic(&|fid| ctx.is_func_monadic(fid));
            let is_monadic = cond_is_monadic || body_is_monadic;

            if is_monadic {
                ctx.write(&format!("whileLoop (fun ({}) =>\n", vars.join(", ")));
                ctx.indent();
                // The condition function must return Except AbortCode Bool
                // If condition is not monadic, wrap with pure
                render_monadic(cond, ctx);
                ctx.dedent();
                ctx.write(&format!(") (fun ({}) =>\n", vars.join(", ")));
                ctx.indent();
                // For monadic while body, we need to append the result tuple inside the do block
                // Use render_as_single_expr which properly handles monadic blocks
                let result_tuple = IRNode::Tuple(vars.iter().map(|v| IRNode::Var(v.clone())).collect());
                let body_with_result = match body.as_ref() {
                    IRNode::Block { children } => {
                        let mut new_children = children.clone();
                        new_children.push(result_tuple);
                        IRNode::Block { children: new_children }
                    }
                    _ => IRNode::Block { children: vec![body.as_ref().clone(), result_tuple] }
                };
                render_as_single_expr(&body_with_result, ctx, true);
                ctx.dedent();
                ctx.write(&format!(") ({})", vars.join(", ")));
            } else {
                // Use whileLoopPure for non-monadic loops, wrapped in Id.run
                ctx.write("Id.run (whileLoopPure (fun (");
                ctx.write(&vars.join(", "));
                ctx.write(") =>\n");
                ctx.indent();
                render(cond, ctx);
                ctx.dedent();
                ctx.write(&format!(") (fun ({}) =>\n", vars.join(", ")));
                ctx.indent();
                render(body, ctx);
                ctx.newline();
                ctx.write(&format!("({})", vars.join(", ")));
                ctx.dedent();
                ctx.write(&format!(") ({}))", vars.join(", ")));
            }
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

/// Check if a node represents a direct monadic call (possibly wrapped in Return)
/// This is used to determine if we need `let _ ←` binding
fn is_direct_monadic_call<W: Write>(node: &IRNode, ctx: &RenderCtx<W>) -> bool {
    match node {
        IRNode::Call { function, .. } => ctx.is_func_monadic(*function),
        IRNode::Return(values) if values.len() == 1 => is_direct_monadic_call(&values[0], ctx),
        _ => false,
    }
}

/// Render an IR node in a monadic context, wrapping with `pure` if the value is not monadic
pub(crate) fn render_monadic<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    // Let nodes should never be wrapped with pure - they're bindings, not values
    if matches!(ir, IRNode::Let { .. }) {
        render(ir, ctx);
        return;
    }

    let is_monadic = ir.is_monadic(&|fid| ctx.is_func_monadic(fid));

    if !is_monadic {
        ctx.write("pure (");
        render(ir, ctx);
        ctx.write(")");
    } else {
        render(ir, ctx);
    }
}

/// Render an IR node as a single expression suitable for if-then-else branches.
/// If the node is a Block with multiple statements, wrap it appropriately.
/// If in_monadic_context is true, ensures the final value is properly wrapped for monadic use.
fn render_as_single_expr<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>, in_monadic_context: bool) {
    match ir {
        IRNode::Block { children } if children.len() > 1 => {
            // Filter out spec nodes and empty blocks
            let filtered_children: Vec<&IRNode> = children.iter()
                .filter(|c| !matches!(c, IRNode::Requires(_) | IRNode::Ensures(_)))
                .filter(|c| !matches!(c, IRNode::Block { children } if children.is_empty()))
                .collect();

            // Multiple statements - check if monadic
            let is_monadic = filtered_children.iter().any(|c| c.contains_monadic(&|fid| ctx.is_func_monadic(fid)));
            if is_monadic || in_monadic_context {
                ctx.write("do\n");
                ctx.indent();
                for (i, child) in filtered_children.iter().enumerate() {
                    let is_last = i == filtered_children.len() - 1;

                    if is_last && in_monadic_context {
                        // Last child in monadic context - use monadic rendering
                        render_monadic(child, ctx);
                    } else if !is_last && (is_monadic || in_monadic_context) {
                        // Non-final child in monadic context
                        // If it's a monadic Call (possibly wrapped in Return), bind it with let _ ←
                        if is_direct_monadic_call(child, ctx) {
                            ctx.write("let _ ← ");
                        }
                        render(child, ctx);
                    } else {
                        render(child, ctx);
                    }
                    if i < children.len() - 1 {
                        ctx.newline();
                    }
                }
                ctx.dedent();
            } else {
                // Non-monadic block with multiple statements
                // Check if all children except last are Let statements
                let non_let_before_last = filtered_children[..filtered_children.len()-1].iter()
                    .any(|c| !matches!(c, IRNode::Let { .. }));

                if non_let_before_last {
                    // Has non-Let statements before last - render only the last child
                    // (earlier statements should have been optimized away or are unreachable)
                    render(filtered_children.last().unwrap(), ctx);
                } else {
                    // All statements before last are Lets - render them all with newlines
                    for (i, child) in filtered_children.iter().enumerate() {
                        render(child, ctx);
                        if i < filtered_children.len() - 1 {
                            ctx.newline();
                        }
                    }
                }
            }
        }
        _ => {
            if in_monadic_context {
                render_monadic(ir, ctx);
            } else {
                render(ir, ctx);
            }
        }
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
        Const::Vector { elems, .. } => {
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
