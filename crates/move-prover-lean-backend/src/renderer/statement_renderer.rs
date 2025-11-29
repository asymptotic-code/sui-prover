// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Statement IR to Lean syntax.
//! Pure translation - pattern match IR nodes to Lean text.
//!
//! Uses LeanWriter which handles both multi-line (indented) and inline (semicolon-separated) modes.

use std::fmt::Write;
use intermediate_theorem_format::{Statement, Expression, Block, TheoremType, ConstantValue, LetPattern, UnOp};
use super::expression_renderer::{RenderCtx, expr_to_string, expr_to_string_atomic, expr_to_string_maybe_monadic, make_pattern};
use super::lean_writer::LeanWriter;
use crate::escape;

/// Render a LetPattern to a Lean pattern string
fn render_pattern(pattern: &LetPattern, ctx: &RenderCtx) -> String {
    match pattern {
        LetPattern::Single(name) => {
            // Use _ for unused variables
            if !ctx.used_vars.contains(name) {
                "_".to_string()
            } else {
                escape::escape_identifier(name)
            }
        }
        LetPattern::Tuple(names) => {
            if names.is_empty() {
                "_".to_string()
            } else {
                let escaped: Vec<_> = names.iter()
                    .map(|n| {
                        if !ctx.used_vars.contains(n) {
                            "_".to_string()
                        } else {
                            escape::escape_identifier(n)
                        }
                    })
                    .collect();
                format!("({})", escaped.join(", "))
            }
        }
    }
}

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

        Statement::Let { pattern, value, types } => {
            // In multi-line mode, if/while get special block rendering
            if !w.is_inline() {
                match value {
                    Expression::IfExpr { condition, then_block, else_block } => {
                        render_if_stmt(pattern, types, condition, then_block, else_block, ctx, w);
                        return;
                    }
                    Expression::WhileExpr { condition, body } => {
                        render_while_stmt(pattern, types, condition, body, ctx, w);
                        return;
                    }
                    _ => {}
                }
            }

            // Normal let binding (or inline mode for if/while)
            let pattern_str = render_pattern(pattern, ctx);
            // Use ← if the expression is monadic based on dynamic purity analysis.
            // This replaces the static type check since pure functions now return
            // plain types even though the IR may still have Except wrapper types.
            // Note: In pure functions (current_function_pure), the entire body is
            // non-monadic so ctx.is_expr_monadic will return false appropriately.
            let is_monadic = ctx.is_expr_monadic(value);
            let bind_op = if is_monadic { "←" } else { ":=" };

            w.write(&format!("let {} {} {}", pattern_str, bind_op, expr_to_string(value, ctx)));
        }

        Statement::Return { values } => {
            // If we're in a pure function, don't wrap with pure - return directly
            if ctx.current_function_pure {
                if values.is_empty() {
                    w.write("()");
                } else if values.len() == 1 {
                    w.write(&expr_to_string(&values[0], ctx));
                } else {
                    w.write("(");
                    for (i, v) in values.iter().enumerate() {
                        if i > 0 {
                            w.write(", ");
                        }
                        w.write(&expr_to_string(v, ctx));
                    }
                    w.write(")");
                }
            } else if values.is_empty() {
                w.write("pure ()");
            } else if values.len() == 1 {
                // Check if this is an IfExpr - always render multi-line for readability
                if !w.is_inline() {
                    if let Expression::IfExpr { condition, then_block, else_block } = &values[0] {
                        // Render as multi-line if-else chain
                        render_return_if(condition, then_block, else_block, ctx, w);
                        return;
                    }
                }
                // Check if the return value is already monadic (e.g., a monadic Call or IfExpr with monadic content)
                // If so, do not wrap with pure - it already produces an Except value
                if ctx.is_expr_monadic(&values[0]) {
                    w.write(&expr_to_string(&values[0], ctx));
                } else {
                    // Value is pure - wrap with pure
                    w.write(&format!("pure {}", expr_to_string_atomic(&values[0], ctx)));
                }
            } else {
                // Multiple return values - check if any is monadic
                let any_monadic = values.iter().any(|v| ctx.is_expr_monadic(v));
                if any_monadic {
                    // Some values are monadic - render without pure wrapper
                    w.write("(");
                    for (i, v) in values.iter().enumerate() {
                        if i > 0 {
                            w.write(", ");
                        }
                        w.write(&expr_to_string(v, ctx));
                    }
                    w.write(")");
                } else {
                    // All values are pure - wrap with pure
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
        }

        Statement::Abort { code } => {
            // AbortCode is Nat, so no conversion needed
            w.write(&format!("Except.error {}", expr_to_string_atomic(code, ctx)));
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

        Statement::Requires { condition } => {
            let cond_str = expr_to_string(condition, ctx);
            w.write(&format!("-- requires: {}", cond_str));
        }

        Statement::Ensures { condition } => {
            let cond_str = expr_to_string(condition, ctx);
            w.write(&format!("-- ensures: {}", cond_str));
        }
    }
}

/// Check if an expression is a boolean constant
fn is_bool_constant(expr: &Expression, expected: bool) -> bool {
    matches!(expr, Expression::Constant(ConstantValue::Bool(b)) if *b == expected)
}

/// Get the effective result of a block, looking through trivial let bindings of constants.
/// This handles the pattern where a block has:
///   statements: [Let { results: [7], operation: Constant(Bool(false)) }]
///   result: Temporary(7)
/// Returns the inlined result expression.
fn get_effective_block_result(block: &Block) -> Option<&Expression> {
    if block.statements.is_empty() {
        // Simple case: no statements, just return the result
        return Some(&block.result);
    }

    // Check if the result is a variable
    if let Expression::Var(result_name) = block.result.as_ref() {
        // Check if all statements are Let bindings of constants for temps that
        // either define the result temp, or define temps only used by other such bindings
        // For simplicity, handle the common case: exactly one Let statement defining the result temp
        if block.statements.len() == 1 {
            if let Statement::Let { pattern: LetPattern::Single(def_name), value, .. } = &block.statements[0] {
                if def_name == result_name {
                    // The only statement defines the result variable
                    return Some(value);
                }
            }
        }
    }

    None
}

/// Check if a block's effective result is a boolean constant
fn block_has_bool_result(block: &Block, expected: bool) -> bool {
    get_effective_block_result(block)
        .map(|result| is_bool_constant(result, expected))
        .unwrap_or(false)
}

/// Check if a block is effectively empty (either no statements, or only trivial constant definitions)
fn block_is_effectively_simple(block: &Block) -> bool {
    if block.statements.is_empty() {
        return true;
    }
    // Check if all statements are trivial Let bindings of constants for temps used only in the result
    get_effective_block_result(block).is_some()
}

/// Result of assertion pattern detection
enum AssertionPattern<'a> {
    /// Pattern: if !cond then abort else () => unless cond do throw code
    Unless { condition: &'a Expression, abort_code: &'a Expression },
    /// Pattern: if cond then abort else () => if cond then throw code
    IfThenThrow { condition: &'a Expression, abort_code: &'a Expression },
}

/// Check if a block is effectively unit (empty tuple result, no statements)
fn is_unit_block(block: &Block) -> bool {
    block.statements.is_empty() &&
    matches!(block.result.as_ref(), Expression::Tuple(elems) if elems.is_empty())
}

/// Extract abort code from a block's statements
fn get_abort_code(block: &Block) -> Option<&Expression> {
    for stmt in &block.statements {
        if let Statement::Abort { code } = stmt {
            return Some(code);
        }
    }
    None
}

/// Try to detect assertion patterns where one branch aborts and the other is unit.
/// Handles both:
///   - if !cond then abort(code) else () => unless cond do throw code
///   - if cond then abort(code) else () => when cond do throw code
fn try_assertion_pattern<'a>(condition: &'a Expression, then_block: &'a Block, else_block: &'a Block, ctx: &RenderCtx) -> Option<AssertionPattern<'a>> {
    // Pattern 1: if !cond then abort else () => unless cond do throw code
    if let Expression::UnOp { op: UnOp::Not, operand } = condition {
        let inner_cond = operand.as_ref();
        // Only use unless for pure conditions
        if !ctx.is_expr_monadic(inner_cond) && !ctx.contains_monadic(inner_cond) {
            if is_unit_block(else_block) {
                if let Some(code) = get_abort_code(then_block) {
                    return Some(AssertionPattern::Unless { condition: inner_cond, abort_code: code });
                }
            }
        }
    }

    // Pattern 2: if cond then abort else () => if cond then throw code
    // Only use this for pure conditions
    if !ctx.is_expr_monadic(condition) && !ctx.contains_monadic(condition) {
        if is_unit_block(else_block) {
            if let Some(code) = get_abort_code(then_block) {
                return Some(AssertionPattern::IfThenThrow { condition, abort_code: code });
            }
        }
    }

    // Pattern 3: if cond then () else abort => unless cond do throw code
    // Only use unless for pure conditions
    if !ctx.is_expr_monadic(condition) && !ctx.contains_monadic(condition) {
        if is_unit_block(then_block) {
            if let Some(code) = get_abort_code(else_block) {
                return Some(AssertionPattern::Unless { condition, abort_code: code });
            }
        }
    }

    None
}

/// Try to simplify short-circuit And pattern: if c1 then c2 else false => c1 && c2
/// Only applies when both operands are pure (non-monadic).
fn try_short_circuit_and(condition: &Expression, then_block: &Block, else_block: &Block, ctx: &RenderCtx) -> Option<Expression> {
    // Check else_block has boolean false result
    if !block_has_bool_result(else_block, false) {
        return None;
    }
    // Check then_block is simple (no complex statements)
    if !block_is_effectively_simple(then_block) {
        return None;
    }
    // Get the effective result of then_block
    let c2 = get_effective_block_result(then_block)?;

    // Only use short-circuit for pure expressions - monadic calls need full if/else
    // because Lean's && returns Bool, not Except
    if ctx.is_expr_monadic(condition) || ctx.contains_monadic(condition) {
        return None;
    }
    if ctx.is_expr_monadic(&c2) || ctx.contains_monadic(&c2) {
        return None;
    }

    Some(c2.clone())
}

/// Try to simplify short-circuit Or pattern: if c1 then true else c2 => c1 || c2
/// Only applies when both operands are pure (non-monadic).
fn try_short_circuit_or(condition: &Expression, then_block: &Block, else_block: &Block, ctx: &RenderCtx) -> Option<Expression> {
    // Check then_block has boolean true result
    if !block_has_bool_result(then_block, true) {
        return None;
    }
    // Check else_block is simple (no complex statements)
    if !block_is_effectively_simple(else_block) {
        return None;
    }
    // Get the effective result of else_block
    let c2 = get_effective_block_result(else_block)?;

    // Only use short-circuit for pure expressions - monadic calls need full if/else
    // because Lean's || returns Bool, not Except
    if ctx.is_expr_monadic(condition) || ctx.contains_monadic(condition) {
        return None;
    }
    if ctx.is_expr_monadic(&c2) || ctx.contains_monadic(&c2) {
        return None;
    }

    Some(c2.clone())
}

/// Render an if expression as a multi-line statement.
fn render_if_stmt<W: Write>(
    pattern: &LetPattern,
    _result_types: &[TheoremType],
    condition: &Expression,
    then_block: &Block,
    else_block: &Block,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    let pattern_str = render_pattern(pattern, ctx);

    // Check for assertion patterns: unless/when cond do throw code
    if let Some(assertion) = try_assertion_pattern(condition, then_block, else_block, ctx) {
        match assertion {
            AssertionPattern::Unless { condition: cond, abort_code } => {
                let cond_str = expr_to_string_maybe_monadic(cond, ctx);
                let code_str = expr_to_string_atomic(abort_code, ctx);
                w.write(&format!("unless {} do throw {}", cond_str, code_str));
            }
            AssertionPattern::IfThenThrow { condition: cond, abort_code } => {
                let cond_str = expr_to_string_maybe_monadic(cond, ctx);
                let code_str = expr_to_string_atomic(abort_code, ctx);
                w.write(&format!("if {} then throw {}", cond_str, code_str));
            }
        }
        return;
    }

    // Check for short-circuit And pattern: if c1 then c2 else false => let x := c1 && c2
    // Only applies for pure (non-monadic) expressions
    if let Some(c2) = try_short_circuit_and(condition, then_block, else_block, ctx) {
        let cond_str = expr_to_string(condition, ctx);
        let c2_str = expr_to_string(&c2, ctx);
        w.write(&format!("let {} := {} && {}", pattern_str, cond_str, c2_str));
        return;
    }

    // Check for short-circuit Or pattern: if c1 then true else c2 => let x := c1 || c2
    // Only applies for pure (non-monadic) expressions
    if let Some(c2) = try_short_circuit_or(condition, then_block, else_block, ctx) {
        let cond_str = expr_to_string(condition, ctx);
        let c2_str = expr_to_string(&c2, ctx);
        w.write(&format!("let {} := {} || {}", pattern_str, cond_str, c2_str));
        return;
    }

    // Check if any branch is monadic or contains monadic subexpressions
    let then_monadic = ctx.is_block_monadic(then_block)
        || ctx.contains_monadic(&then_block.result);
    let else_monadic = ctx.is_block_monadic(else_block)
        || ctx.contains_monadic(&else_block.result);
    let any_monadic = then_monadic || else_monadic;

    // Check if the condition itself is monadic (or contains monadic) - needs ← prefix
    let condition_is_monadic = ctx.is_expr_monadic(condition) || ctx.contains_monadic(condition);
    // Use expr_to_string_maybe_monadic for conditions that are monadic calls
    let cond_str = if condition_is_monadic || any_monadic {
        expr_to_string_maybe_monadic(condition, ctx)
    } else {
        expr_to_string(condition, ctx)
    };

    // Check if both branches terminate
    let both_terminate = then_block.terminates() && else_block.terminates();

    // Determine binding operator
    let bind_op = if any_monadic { "←" } else { ":=" };

    let pattern_is_empty = match pattern {
        LetPattern::Single(_) => false,
        LetPattern::Tuple(names) => names.is_empty(),
    };

    if both_terminate && pattern_is_empty {
        // Terminating if - no binding needed
        w.write(&format!("if {} then", cond_str));
    } else {
        w.write(&format!("let {} {} if {} then", pattern_str, bind_op, cond_str));
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

/// Check if an IfExpr should be rendered multi-line (e.g., has nested IfExpr in else).
fn should_render_multiline_if(else_block: &Block) -> bool {
    // If the else block has a nested IfExpr as its result (else-if chain), render multi-line
    if else_block.statements.is_empty() {
        matches!(else_block.result.as_ref(), Expression::IfExpr { .. })
    } else {
        false
    }
}

/// Render a Return statement with an IfExpr as multi-line if-else-if chain.
fn render_return_if<W: Write>(
    condition: &Expression,
    then_block: &Block,
    else_block: &Block,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    // Since we're in a function that returns Except (we're in a do-block),
    // we always need monadic treatment for the return values.
    // Pure branches will get wrapped with `pure`.
    let need_monadic = true;

    // Check if the condition itself is monadic
    let condition_is_monadic = ctx.is_expr_monadic(condition) || ctx.contains_monadic(condition);
    let cond_str = if condition_is_monadic {
        expr_to_string_maybe_monadic(condition, ctx)
    } else {
        expr_to_string(condition, ctx)
    };

    // Start the if expression
    w.write(&format!("if {} then", cond_str));
    w.write("\n");

    // Then branch
    w.indent();
    render_block(then_block, need_monadic, ctx, w);
    w.dedent();

    // Else branch - handle else-if chains
    render_else_chain(else_block, need_monadic, ctx, w);
}

/// Render the else part of an if chain, flattening else-if patterns.
fn render_else_chain<W: Write>(
    else_block: &Block,
    need_monadic: bool,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    // Check if this is an else-if (else block has no statements and result is IfExpr)
    if else_block.statements.is_empty() {
        if let Expression::IfExpr { condition, then_block, else_block: nested_else } = else_block.result.as_ref() {
            // Check if the condition is monadic
            let condition_is_monadic = ctx.is_expr_monadic(condition) || ctx.contains_monadic(condition);
            let cond_str = if condition_is_monadic {
                expr_to_string_maybe_monadic(condition, ctx)
            } else {
                expr_to_string(condition, ctx)
            };

            w.write(&format!("\nelse if {} then", cond_str));
            w.write("\n");

            // Then branch
            w.indent();
            render_block(then_block, need_monadic, ctx, w);
            w.dedent();

            // Recurse for potential else-if chains
            render_else_chain(nested_else, need_monadic, ctx, w);
            return;
        }
    }

    // Regular else block
    w.write("\nelse\n");
    w.indent();
    render_block(else_block, need_monadic, ctx, w);
    w.dedent();
}

/// Derive loop state variable names from the body's result expression.
/// The variables referenced in the result are the loop-carried state.
/// For tuples, extracts vars in tuple order (not depth-first traversal order).
fn derive_state_vars(body: &Block) -> Vec<String> {
    extract_top_level_vars(&body.result)
}

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

/// Render a while expression as a multi-line statement.
fn render_while_stmt<W: Write>(
    pattern: &LetPattern,
    _result_types: &[TheoremType],
    condition: &Block,
    body: &Block,
    ctx: &RenderCtx,
    w: &mut LeanWriter<W>,
) {
    // Derive state variables from body result
    let state_vars = derive_state_vars(body);

    // Render the result pattern (what the while loop binds to)
    let pattern_str = render_pattern(pattern, ctx);
    // State pattern uses the loop state variable names
    let state_pattern = make_pattern(&state_vars);

    // Initial values are just the same variable names (referencing outer scope)
    let init_str = if state_vars.is_empty() {
        "()".to_string()
    } else if state_vars.len() == 1 {
        escape::escape_identifier(&state_vars[0])
    } else {
        let vals: Vec<_> = state_vars.iter().map(|v| escape::escape_identifier(v)).collect();
        format!("({})", vals.join(", "))
    };

    w.write(&format!("let {} ← (whileLoop (fun {} =>", pattern_str, state_pattern));
    w.write("\n");
    w.indent();
    w.write("do\n");
    w.indent();

    // Condition block
    render_block_statements(&condition.statements, ctx, w);
    if !condition.statements.is_empty() {
        w.write("\n");
    }
    let cond_result = expr_to_string_atomic(&condition.result, ctx);
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
    let body_result = expr_to_string_atomic(&body.result, ctx);
    w.write(&format!("pure {}", body_result));

    w.dedent();
    w.dedent();
    w.write(&format!(") {})", init_str));
}

/// Render a block with proper indentation.
fn render_block<W: Write>(block: &Block, need_monadic: bool, ctx: &RenderCtx, w: &mut LeanWriter<W>) {
    let block_is_monadic = ctx.is_block_monadic(block);
    let result_contains_monadic = ctx.contains_monadic(&block.result);

    if block.statements.is_empty() {
        // Simple block - just result
        if ctx.is_expr_monadic(&block.result) {
            // Result is monadic - render directly (no pure wrapper)
            let result_str = expr_to_string(&block.result, ctx);
            w.write(&result_str);
        } else if need_monadic {
            // Result is pure but we need monadic - wrap with pure
            // If result contains_monadic, the ← bindings are inside, but result is still pure
            w.write("pure ");
            let result_str = expr_to_string_atomic(&block.result, ctx);
            w.write(&result_str);
        } else {
            let result_str = expr_to_string(&block.result, ctx);
            w.write(&result_str);
        }
    } else if need_monadic || block_is_monadic || result_contains_monadic {
        // Monadic block with statements - use do notation
        w.write("do\n");
        w.indent();

        render_block_statements(&block.statements, ctx, w);

        // Result
        if !block.terminates() {
            w.write("\n");
            if ctx.is_expr_monadic(&block.result) {
                // Result is monadic - render directly
                let result_str = expr_to_string(&block.result, ctx);
                w.write(&result_str);
            } else {
                // Result is pure - wrap with pure
                w.write("pure ");
                let result_str = expr_to_string_atomic(&block.result, ctx);
                w.write(&result_str);
            }
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
            let result_str = expr_to_string_atomic(&block.result, ctx);
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
