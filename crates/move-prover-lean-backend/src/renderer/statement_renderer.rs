// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Statement IR to Lean syntax.
//! Pure translation - pattern match IR nodes to Lean text.
//!
//! Uses LeanWriter which handles both multi-line (indented) and inline (semicolon-separated) modes.

use std::fmt::Write;
use intermediate_theorem_format::{Statement, Expression, Block, TempId, TheoremType, LoopState};
use super::expression_renderer::{RenderCtx, expr_to_string, make_pattern};
use super::lean_writer::LeanWriter;

/// Render a statement.
/// In inline mode (LeanWriter::is_inline()), renders semicolon-separated without special if/while handling.
/// In multi-line mode, renders with proper indentation and expands if/while to block form.
pub fn render_stmt<W: Write>(stmt: &Statement, ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    match stmt {
        Statement::Sequence(stmts) => {
            if stmts.is_empty() {
                w.write("pure ()");
            } else {
                for (i, s) in stmts.iter().enumerate() {
                    render_stmt(s, ctx, w);
                    // Stop at terminators
                    if matches!(s, Statement::Return { .. } | Statement::Abort { .. }) {
                        break;
                    }
                    if i < stmts.len() - 1 {
                        w.write("\n");
                    }
                }
            }
        }

        Statement::Let { results, operation, result_types } => {
            // In multi-line mode, if/while get special block rendering
            if !w.is_inline() {
                match operation {
                    Expression::IfExpr { condition, then_block, else_block } => {
                        render_if_stmt(results, result_types, condition, then_block, else_block, ctx, w);
                        return;
                    }
                    Expression::WhileExpr { condition, body, state } => {
                        render_while_stmt(results, result_types, condition, body, state, ctx, w);
                        return;
                    }
                    _ => {}
                }
            }

            // Normal let binding (or inline mode for if/while)
            let pattern = make_pattern(results, ctx.registry);
            let is_monadic = result_types.iter().any(|ty| ty.is_monad()) || operation.is_monadic();
            let bind_op = if is_monadic { "←" } else { ":=" };

            w.write(&format!("let {} {} {}", pattern, bind_op, expr_to_string(operation, ctx)));
        }

        Statement::Return { values } => {
            if values.is_empty() {
                w.write("pure ()");
            } else if values.len() == 1 {
                w.write(&format!("pure {}", expr_to_string(&values[0], ctx)));
            } else {
                w.write("pure (");
                for (i, v) in values.iter().enumerate() {
                    if i > 0 {
                        w.write(", ");
                    }
                    w.write(&expr_to_string(v, ctx));
                }
                w.write(")");
            }
        }

        Statement::Abort { code } => {
            w.write(&format!("Except.error ({}).toNat", expr_to_string(code, ctx)));
        }

        Statement::UpdateField { target, struct_id, field_index, new_value } => {
            let target_str = expr_to_string(target, ctx);
            let struct_info = ctx.program.structs.get(struct_id)
                .unwrap_or_else(|| panic!("Missing struct info for ID: {}", struct_id));
            let field_name = &struct_info.fields[*field_index].name;
            let value_str = expr_to_string(new_value, ctx);

            w.write(&format!("let {} := {{ {} with {} := {} }}", target_str, target_str, field_name, value_str));
        }

        Statement::UpdateVectorElement { target, index, new_value } => {
            let target_str = expr_to_string(target, ctx);
            let index_str = expr_to_string(index, ctx);
            let value_str = expr_to_string(new_value, ctx);

            w.write(&format!("let {} := {}.set {} {}", target_str, target_str, index_str, value_str));
        }

        Statement::Requires { .. } | Statement::Ensures { .. } => {
            w.write("pure ()");
        }
    }
}

/// Render an if expression as a multi-line statement.
fn render_if_stmt<W: Write>(
    results: &[TempId],
    _result_types: &[TheoremType],
    condition: &Expression,
    then_block: &Block,
    else_block: &Block,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let cond_str = expr_to_string(condition, ctx);
    let pattern = make_pattern(results, ctx.registry);

    // Check if any branch is monadic
    let then_monadic = then_block.is_monadic() || then_block.result.is_monadic();
    let else_monadic = else_block.is_monadic() || else_block.result.is_monadic();
    let any_monadic = then_monadic || else_monadic;

    // Check if both branches terminate
    let both_terminate = then_block.terminates() && else_block.terminates();

    // Determine binding operator
    let bind_op = if any_monadic { "←" } else { ":=" };

    if both_terminate && results.is_empty() {
        // Terminating if - no binding needed
        w.write(&format!("if {} then", cond_str));
    } else {
        w.write(&format!("let {} {} if {} then", pattern, bind_op, cond_str));
    }
    w.write("\n");

    // Then branch
    w.indent();
    render_block(then_block, any_monadic, ctx, w);
    w.dedent();

    w.write("\nelse\n");

    // Else branch
    w.indent();
    render_block(else_block, any_monadic, ctx, w);
    w.dedent();
}

/// Render a while expression as a multi-line statement.
fn render_while_stmt<W: Write>(
    results: &[TempId],
    _result_types: &[TheoremType],
    condition: &Block,
    body: &Block,
    state: &LoopState,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let pattern = make_pattern(results, ctx.registry);
    let state_pattern = make_pattern(&state.vars, ctx.registry);

    // Initial values
    let init_str = if state.initial.is_empty() {
        "()".to_string()
    } else if state.initial.len() == 1 {
        expr_to_string(&state.initial[0], ctx)
    } else {
        let vals: Vec<_> = state.initial.iter().map(|e| expr_to_string(e, ctx)).collect();
        format!("({})", vals.join(", "))
    };

    w.write(&format!("let {} ← (whileLoop (fun {} =>", pattern, state_pattern));
    w.write("\n");
    w.indent();
    w.write("do\n");
    w.indent();

    // Condition block
    render_block_statements(&condition.statements, ctx, w);
    if !condition.statements.is_empty() {
        w.write("\n");
    }
    let cond_result = expr_to_string(&condition.result, ctx);
    w.write(&format!("pure {}", cond_result));

    w.dedent();
    w.dedent();
    w.write(&format!(") (fun {} =>", state_pattern));
    w.write("\n");
    w.indent();
    w.write("do\n");
    w.indent();

    // Body block
    render_block_statements(&body.statements, ctx, w);
    if !body.statements.is_empty() {
        w.write("\n");
    }
    let body_result = expr_to_string(&body.result, ctx);
    w.write(&format!("pure {}", body_result));

    w.dedent();
    w.dedent();
    w.write(&format!(") {})", init_str));
}

/// Render a block with proper indentation.
fn render_block<W: Write>(block: &Block, need_monadic: bool, ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    let block_is_monadic = block.is_monadic() || block.result.is_monadic();

    if block.statements.is_empty() {
        // Simple block - just result
        if need_monadic && !block.result.is_monadic() {
            w.write("pure ");
        }
        let result_str = expr_to_string(&block.result, ctx);
        w.write(&result_str);
    } else if need_monadic || block_is_monadic {
        // Monadic block with statements - use do notation
        w.write("do\n");
        w.indent();

        render_block_statements(&block.statements, ctx, w);

        // Result
        if !block.terminates() {
            w.write("\n");
            if !block.result.is_monadic() {
                w.write("pure ");
            }
            let result_str = expr_to_string(&block.result, ctx);
            w.write(&result_str);
        }

        w.dedent();
    } else {
        // Pure block with statements - use Id.run do
        w.write("Id.run do\n");
        w.indent();

        render_block_statements(&block.statements, ctx, w);

        // Result
        if !block.terminates() {
            w.write("\n");
            w.write("pure ");
            let result_str = expr_to_string(&block.result, ctx);
            w.write(&result_str);
        }

        w.dedent();
    }
}

/// Render block statements.
fn render_block_statements<W: Write>(statements: &[Statement], ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    for (i, stmt) in statements.iter().enumerate() {
        render_stmt(stmt, ctx, w);
        if i < statements.len() - 1 {
            w.write("\n");
        }
    }
}
