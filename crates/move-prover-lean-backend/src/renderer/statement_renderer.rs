// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders IR statements to Lean syntax.
//! Pure translation - pattern match IR nodes to Lean text.
//!
//! Uses LeanWriter which handles both multi-line (indented) and inline (semicolon-separated) modes.

use super::expression_renderer::{
    contains_call_monadic, ir_to_string, ir_to_string_atomic, ir_to_string_maybe_monadic,
    render_ir, render_pattern, RenderCtx,
};
use super::lean_writer::LeanWriter;
use crate::escape;
use intermediate_theorem_format::IRNode;
use std::fmt::Write;

/// Check if an IR node is a monadic expression (directly returns Except).
/// Delegates to the IR's is_monadic method.
fn is_call_monadic_stmt(ir: &IRNode, ctx: &RenderCtx) -> bool {
    ir.is_monadic(&|fid| ctx.is_func_monadic(fid))
}

/// Render a statement (IR node in statement position).
pub fn render_stmt<W: Write>(ir: &IRNode, ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    match ir {
        IRNode::Let { pattern, value, .. } => {
            // In multi-line mode, if/while get special block rendering
            if !w.is_inline() {
                match value.as_ref() {
                    IRNode::If {
                        cond,
                        then_branch,
                        else_branch,
                    } => {
                        render_if_stmt(pattern, cond, then_branch, else_branch, ctx, w);
                        return;
                    }
                    IRNode::While { cond, body, vars } => {
                        render_while_stmt(pattern, cond, body, vars, ctx, w);
                        return;
                    }
                    _ => {}
                }
            }

            // Normal let binding
            let pattern_str = render_pattern(pattern);
            // Use is_call_monadic_stmt to properly check the function's return type
            let is_monadic = is_call_monadic_stmt(value, ctx);
            let bind_op = if is_monadic { "←" } else { ":=" };

            w.write(&format!(
                "let {} {} {}",
                pattern_str,
                bind_op,
                ir_to_string(value, ctx)
            ));
        }

        IRNode::Return(values) => {
            if !ctx.current_function_monadic {
                if values.is_empty() {
                    w.write("()");
                } else if values.len() == 1 {
                    w.write(&ir_to_string(&values[0], ctx));
                } else {
                    w.write("(");
                    for (i, v) in values.iter().enumerate() {
                        if i > 0 {
                            w.write(", ");
                        }
                        w.write(&ir_to_string(v, ctx));
                    }
                    w.write(")");
                }
            } else if values.is_empty() {
                w.write("pure ()");
            } else if values.len() == 1 {
                // Check for IfExpr - render multi-line
                if !w.is_inline() {
                    if let IRNode::If {
                        cond,
                        then_branch,
                        else_branch,
                    } = &values[0]
                    {
                        render_return_if(cond, then_branch, else_branch, ctx, w);
                        return;
                    }
                }
                if is_call_monadic_stmt(&values[0], ctx) {
                    w.write(&ir_to_string(&values[0], ctx));
                } else {
                    w.write(&format!("pure {}", ir_to_string_atomic(&values[0], ctx)));
                }
            } else {
                let any_monadic = values.iter().any(|v| is_call_monadic_stmt(v, ctx));
                if any_monadic {
                    // Sequence monadic elements: (e1, e2) where e1 is monadic becomes (do let x ← e1; pure (x, e2))
                    w.write("(do ");
                    let mut temp_names = Vec::new();
                    for (i, v) in values.iter().enumerate() {
                        if is_call_monadic_stmt(v, ctx) {
                            let temp_name = format!("__ret_{}", i);
                            w.write(&format!("let {} ← ", temp_name));
                            w.write(&ir_to_string(v, ctx));
                            w.write("; ");
                            temp_names.push(temp_name);
                        } else {
                            temp_names.push(String::new());
                        }
                    }
                    w.write("pure (");
                    for (i, v) in values.iter().enumerate() {
                        if i > 0 {
                            w.write(", ");
                        }
                        if !temp_names[i].is_empty() {
                            w.write(&temp_names[i]);
                        } else {
                            w.write(&ir_to_string(v, ctx));
                        }
                    }
                    w.write("))");
                } else {
                    w.write("pure (");
                    for (i, v) in values.iter().enumerate() {
                        if i > 0 {
                            w.write(", ");
                        }
                        w.write(&ir_to_string(v, ctx));
                    }
                    w.write(")");
                }
            }
        }

        IRNode::Abort(code) => {
            w.write(&format!("Except.error {}", ir_to_string_atomic(code, ctx)));
        }

        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => {
            let target_str = ir_to_string(base, ctx);
            let field_name = ctx.program.structs.get(struct_id).fields[*field_index]
                .name
                .clone();
            let value_str = ir_to_string(value, ctx);

            w.write(&format!(
                "let {} := {{ {} with {} := {} }}",
                target_str, target_str, field_name, value_str
            ));
        }

        IRNode::UpdateVec { base, index, value } => {
            let target_str = ir_to_string(base, ctx);
            let index_str = ir_to_string(index, ctx);
            let value_str = ir_to_string(value, ctx);

            w.write(&format!(
                "let {} := {}.set {} {}",
                target_str, target_str, index_str, value_str
            ));
        }

        IRNode::Requires(cond) => {
            let cond_str = ir_to_string(cond, ctx);
            w.write(&format!("-- requires: {}", cond_str));
        }

        IRNode::Ensures(cond) => {
            let cond_str = ir_to_string(cond, ctx);
            w.write(&format!("-- ensures: {}", cond_str));
        }

        // Bare If expression in statement position - render multi-line
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } if !w.is_inline() => {
            render_if_stmt(&[], cond, then_branch, else_branch, ctx, w);
        }

        // Other IR nodes that appear in statement position
        _ => {
            // For other expressions in statement position, just render them
            let mut s = String::new();
            render_ir(ir, ctx, &mut s);
            w.write(&s);
        }
    }
}

/// Render an if expression as a multi-line statement.
fn render_if_stmt<W: Write>(
    pattern: &[String],
    cond: &IRNode,
    then_branch: &IRNode,
    else_branch: &IRNode,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let pattern_str = render_pattern(pattern);
    let then_monadic = contains_call_monadic(then_branch, ctx);
    let else_monadic = contains_call_monadic(else_branch, ctx);
    let any_monadic = then_monadic || else_monadic;

    let cond_str = ir_to_string_maybe_monadic(cond, ctx);

    let both_terminate = then_branch.terminates() && else_branch.terminates();
    let need_monadic = any_monadic || ctx.current_function_monadic;
    let bind_op = if need_monadic { "←" } else { ":=" };
    let pattern_is_empty = pattern.is_empty();

    // Skip let binding when:
    // 1. Both branches terminate (Return/Abort), OR
    // 2. Pattern is empty (value is being returned, not bound)
    if both_terminate || pattern_is_empty {
        w.write(&format!("if {} then", cond_str));
    } else {
        w.write(&format!(
            "let {} {} if {} then",
            pattern_str, bind_op, cond_str
        ));
    }
    w.write("\n");

    w.indent();
    render_block(then_branch, need_monadic, ctx, w);
    w.dedent();

    w.write("\nelse\n");

    w.indent();
    render_block(else_branch, need_monadic, ctx, w);
    w.dedent();
}

/// Render a Return statement with an IfExpr as multi-line if-else-if chain.
fn render_return_if<W: Write>(
    cond: &IRNode,
    then_branch: &IRNode,
    else_branch: &IRNode,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let need_monadic = true;
    let cond_str = ir_to_string_maybe_monadic(cond, ctx);

    w.write(&format!("if {} then", cond_str));
    w.write("\n");

    w.indent();
    render_block(then_branch, need_monadic, ctx, w);
    w.dedent();

    render_else_chain(else_branch, need_monadic, ctx, w);
}

/// Render the else part of an if chain, flattening else-if patterns.
fn render_else_chain<W: Write>(
    else_branch: &IRNode,
    need_monadic: bool,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    // Check for else-if (Block with no statements and result is If)
    if let IRNode::Block { children } = else_branch {
        if children.len() == 1 {
            if let IRNode::If {
                cond,
                then_branch,
                else_branch: nested_else,
            } = &children[0]
            {
                let cond_str = ir_to_string_maybe_monadic(cond, ctx);
                w.write(&format!("\nelse if {} then", cond_str));
                w.write("\n");

                w.indent();
                render_block(then_branch, need_monadic, ctx, w);
                w.dedent();

                render_else_chain(nested_else, need_monadic, ctx, w);
                return;
            }
        }
    }

    // Regular else block
    w.write("\nelse\n");
    w.indent();
    render_block(else_branch, need_monadic, ctx, w);
    w.dedent();
}

/// Construct a tuple of variable references from a list of variable names
fn construct_var_tuple(vars: &[String], _ctx: &RenderCtx) -> IRNode {
    if vars.is_empty() {
        IRNode::Tuple(vec![])
    } else if vars.len() == 1 {
        IRNode::Var(vars[0].clone())
    } else {
        IRNode::Tuple(vars.iter().map(|v| IRNode::Var(v.clone())).collect())
    }
}

/// Render a while expression as a multi-line statement.
fn render_while_stmt<W: Write>(
    pattern: &[String],
    cond: &IRNode,
    body: &IRNode,
    vars: &[String],
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let pattern_str = render_pattern(pattern);
    let state_pattern = render_pattern(vars);
    // For initial state: use `default` for temps (starting with $t), actual var reference for real vars
    let init_str = super::render_tuple_like(vars, "()", ", ", |v| {
        if v.starts_with("$t") {
            "default".to_string()
        } else {
            escape::escape_identifier(v)
        }
    });

    // Use whileLoop for monadic loops, whileLoopPure for pure loops
    let is_monadic = contains_call_monadic(body, ctx) || contains_call_monadic(cond, ctx);
    let (bind_op, loop_fn) = if is_monadic {
        ("←", "whileLoop")
    } else {
        (":=", "whileLoopPure")
    };
    w.write(&format!(
        "let {} {} ({} (fun {} =>",
        pattern_str, bind_op, loop_fn, state_pattern
    ));
    w.write("\n");
    w.indent();
    w.write("do\n");
    w.indent();

    // Condition block
    render_block_statements(cond, ctx, w);
    let cond_result = cond.get_block_result();
    // If the result is monadic, render it directly. Otherwise, wrap in pure.
    if is_call_monadic_stmt(cond_result, ctx) {
        w.write(&ir_to_string(cond_result, ctx));
    } else {
        w.write(&format!("pure {}", ir_to_string_atomic(cond_result, ctx)));
    }

    w.dedent();
    w.dedent();
    w.write(&format!(") (fun {} =>", state_pattern));
    w.write("\n");
    w.indent();
    w.write("do\n");
    w.indent();

    // Body block - render all statements
    render_block_statements(body, ctx, w);

    // Construct the return tuple from vars
    // The body should return the loop state variables as a tuple
    let return_tuple = construct_var_tuple(vars, ctx);

    // If the return tuple is monadic (contains monadic elements), render it directly.
    // Otherwise, wrap in pure.
    if is_call_monadic_stmt(&return_tuple, ctx) {
        w.write(&ir_to_string(&return_tuple, ctx));
    } else {
        w.write(&format!("pure {}", ir_to_string_atomic(&return_tuple, ctx)));
    }

    w.dedent();
    w.dedent();
    w.write(&format!(") {})", init_str));
}

/// Render an expression result, wrapping in pure if needed
fn render_result<W: Write>(
    result: &IRNode,
    need_monadic: bool,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    // Complex structures (If/While) should be rendered as statements for readability
    if should_render_as_stmt(result) {
        render_stmt(result, ctx, w);
    } else if result.terminates() {
        render_stmt(result, ctx, w);
    } else if is_call_monadic_stmt(result, ctx) {
        w.write(&ir_to_string(result, ctx));
    } else if need_monadic {
        w.write("pure ");
        w.write(&ir_to_string_atomic(result, ctx));
    } else {
        w.write(&ir_to_string(result, ctx));
    }
}

/// Render statements with newlines between them
fn render_stmts<W: Write>(stmts: &[IRNode], ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    for (i, stmt) in stmts.iter().enumerate() {
        render_stmt(stmt, ctx, w);
        if i < stmts.len() - 1 {
            w.write("\n");
        }
    }
}

/// Check if an IR node should be rendered as a statement (multi-line) rather than inline.
/// This is true for Let bindings with complex values like If/While.
fn should_render_as_stmt(ir: &IRNode) -> bool {
    match ir {
        IRNode::Let { value, .. } => {
            matches!(
                value.as_ref(),
                IRNode::If { .. } | IRNode::While { .. } | IRNode::Block { .. }
            )
        }
        IRNode::If { .. } | IRNode::While { .. } => true,
        _ => false,
    }
}

/// Render a block with proper indentation.
pub fn render_block<W: Write>(
    ir: &IRNode,
    need_monadic: bool,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let stmts = ir.get_block_stmts();
    let result = ir.get_block_result();

    // Empty block
    if ir.is_unit() && stmts.is_empty() {
        w.write("sorry");
        return;
    }

    // Simple block - just result (no statements)
    if stmts.is_empty() {
        // If result is a complex structure (Let with If/While), render as statements
        if should_render_as_stmt(result) {
            let is_monadic = need_monadic || contains_call_monadic(result, ctx);
            if is_monadic {
                w.write("do\n");
            } else {
                w.write("Id.run do\n");
            }
            w.indent();
            render_stmt(result, ctx, w);
            w.dedent();
            return;
        }

        // Check if result contains monadic subexpressions that need do block
        if need_monadic && contains_call_monadic(result, ctx) && !is_call_monadic_stmt(result, ctx)
        {
            // Need do block to handle monadic subexpressions
            w.write("do\n");
            w.indent();
            render_result(result, true, ctx, w);
            w.dedent();
        } else {
            render_result(result, need_monadic, ctx, w);
        }
        return;
    }

    // Block with statements
    let is_monadic = need_monadic
        || stmts.iter().any(|s| contains_call_monadic(s, ctx))
        || contains_call_monadic(result, ctx);

    if is_monadic {
        w.write("do\n");
    } else {
        w.write("Id.run do\n");
    }

    w.indent();
    render_stmts(stmts, ctx, w);
    w.write("\n");
    render_result(result, is_monadic, ctx, w);
    w.dedent();
}

/// Render block statements (all but last child).
fn render_block_statements<W: Write>(ir: &IRNode, ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    let stmts = ir.get_block_stmts();
    if !stmts.is_empty() {
        render_stmts(stmts, ctx, w);
        w.write("\n");
    }
}
