// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Statement rendering - renders IR nodes in statement position with proper indentation

use super::context::RenderCtx;
use super::expr::{render, render_parens, render_to_string, render_with_arrow_to_string};
use super::helpers::*;
use intermediate_theorem_format::IRNode;
use std::fmt::Write;

/// Render an IR node in statement position (multi-line with indentation)
pub fn render_stmt<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    render_stmt_with_context(ir, false, ctx);
}

fn render_stmt_with_context<W: Write>(ir: &IRNode, in_monadic_block: bool, ctx: &mut RenderCtx<W>) {
    match ir {
        IRNode::Let { pattern, value, .. } => render_let(pattern, value, ctx),
        IRNode::Return(values) => render_return(values, in_monadic_block, ctx),
        IRNode::Abort(code) => {
            ctx.write("Except.error ");
            render_parens(code, ctx);
        }
        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => render_update_field_stmt(*struct_id, *field_index, base, value, ctx),
        IRNode::UpdateVec { base, index, value } => render_update_vec_stmt(base, index, value, ctx),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => render_if_stmt(None, cond, then_branch, else_branch, ctx),
        IRNode::While { cond, body, vars } => render_while_stmt(None, cond, body, vars, ctx),
        IRNode::Requires(cond) => {
            ctx.write("-- requires: ");
            render(cond, ctx);
        }
        IRNode::Ensures(cond) => {
            ctx.write("-- ensures: ");
            render(cond, ctx);
        }
        // Expressions in statement position - just render them
        _ => {
            render(ir, ctx);
        }
    }
}

// ============================================================================
// Let Bindings
// ============================================================================

fn render_let<W: Write>(pattern: &[String], value: &IRNode, ctx: &mut RenderCtx<W>) {
    // Special handling for if/while as values in statement position
    if !ctx.is_inline() {
        match value {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                render_if_stmt(Some(pattern), cond, then_branch, else_branch, ctx);
                return;
            }
            IRNode::While { cond, body, vars } => {
                render_while_stmt(Some(pattern), cond, body, vars, ctx);
                return;
            }
            _ => {}
        }
    }

    // Normal let binding
    let pattern_str = make_pattern(pattern);
    let is_monadic = value.is_monadic(&|fid| ctx.is_func_monadic(fid));
    let op = bind_op(is_monadic);

    ctx.write(&format!("let {} {} ", pattern_str, op));
    render(value, ctx);
}

// ============================================================================
// Return Statements
// ============================================================================

fn render_return<W: Write>(values: &[IRNode], in_monadic_block: bool, ctx: &mut RenderCtx<W>) {
    // Check if we're in a monadic function by looking at the return values
    let any_monadic = values
        .iter()
        .any(|v| v.is_monadic(&|fid| ctx.is_func_monadic(fid)));

    // If we're not in a monadic context and values aren't monadic, render as pure value
    if !in_monadic_block && !any_monadic && values.iter().all(|v| !v.contains_monadic(&|fid| ctx.is_func_monadic(fid))) {
        // Pure return
        render_value_tuple(values, ctx);
        return;
    }

    // Monadic return
    match values {
        [] => ctx.write("pure ()"),
        [single] => {
            // Special case: return if expression in multi-line mode
            if !ctx.is_inline() {
                if let IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                } = single
                {
                    render_return_if(cond, then_branch, else_branch, ctx);
                    return;
                }
            }

            if single.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
                render(single, ctx);
            } else {
                ctx.write("pure ");
                render_parens(single, ctx);
            }
        }
        multiple => {
            if any_monadic {
                render_monadic_return_tuple(multiple, ctx);
            } else {
                ctx.write("pure (");
                render_value_tuple(multiple, ctx);
                ctx.write(")");
            }
        }
    }
}

fn render_value_tuple<W: Write>(values: &[IRNode], ctx: &mut RenderCtx<W>) {
    if values.is_empty() {
        ctx.write("()");
    } else if values.len() == 1 {
        render(&values[0], ctx);
    } else {
        for (i, v) in values.iter().enumerate() {
            if i > 0 { ctx.write(", "); }
            render(v, ctx);
        }
    }
}

fn render_monadic_return_tuple<W: Write>(values: &[IRNode], ctx: &mut RenderCtx<W>) {
    let mut bindings = Vec::new();
    let mut temp_names = Vec::new();

    for (i, v) in values.iter().enumerate() {
        if v.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
            let temp_name = format!("__ret_{}", i);
            bindings.push(format!("let {} ← {}", temp_name, render_to_string(v, ctx)));
            temp_names.push(Some(temp_name));
        } else {
            temp_names.push(None);
        }
    }

    let tuple_elems: Vec<_> = values
        .iter()
        .zip(&temp_names)
        .map(|(v, temp)| {
            temp.as_ref()
                .map(|s| s.clone())
                .unwrap_or_else(|| render_to_string(v, ctx))
        })
        .collect();

    if tuple_elems.len() == 1 && values[0].is_atomic() {
        // Single atomic element - no parens needed
        ctx.write(&format!(
            "(do {}; pure {})",
            bindings.join("; "),
            tuple_elems[0]
        ));
    } else if tuple_elems.is_empty() {
        ctx.write(&format!(
            "(do {}; pure ())",
            bindings.join("; ")
        ));
    } else {
        ctx.write(&format!(
            "(do {}; pure ({}))",
            bindings.join("; "),
            tuple_elems.join(", ")
        ));
    }
}

// ============================================================================
// Field Updates
// ============================================================================

fn render_update_field_stmt<W: Write>(
    struct_id: intermediate_theorem_format::StructID,
    field_index: usize,
    base: &IRNode,
    value: &IRNode,
    ctx: &mut RenderCtx<W>,
) {
    let struct_def = ctx.program.structs.get(struct_id);
    let field_name = &struct_def.fields[field_index].name;
    let target_str = render_to_string(base, ctx);
    let value_str = render_to_string(value, ctx);

    ctx.write(&format!(
        "let {} := {{ {} with {} := {} }}",
        target_str, target_str, field_name, value_str
    ));
}

fn render_update_vec_stmt<W: Write>(
    base: &IRNode,
    index: &IRNode,
    value: &IRNode,
    ctx: &mut RenderCtx<W>,
) {
    let target_str = render_to_string(base, ctx);
    let index_str = render_to_string(index, ctx);
    let value_str = render_to_string(value, ctx);

    ctx.write(&format!(
        "let {} := {}.set {} {}",
        target_str, target_str, index_str, value_str
    ));
}

// ============================================================================
// If Statements
// ============================================================================

fn render_if_stmt<W: Write>(
    pattern: Option<&[String]>,
    cond: &IRNode,
    then_branch: &IRNode,
    else_branch: &IRNode,
    ctx: &mut RenderCtx<W>,
) {
    let has_monadic = then_branch.contains_monadic(&|fid| ctx.is_func_monadic(fid))
        || else_branch.contains_monadic(&|fid| ctx.is_func_monadic(fid));

    let cond_str = render_with_arrow_to_string(cond, ctx);
    let both_terminate = then_branch.terminates() && else_branch.terminates();

    // Determine if we need let binding
    let pattern_str = pattern.map(make_pattern);
    let need_binding = pattern.map_or(false, |p| !p.is_empty()) && !both_terminate;

    if need_binding {
        let op = bind_op(has_monadic);
        ctx.write(&format!(
            "let {} {} if {} then",
            pattern_str.unwrap(),
            op,
            cond_str
        ));
    } else {
        ctx.write(&format!("if {} then", cond_str));
    }

    ctx.write(" ");
    render_branch(then_branch, has_monadic, ctx);

    render_else_chain(else_branch, has_monadic, ctx);
}

/// Render a branch for if-then-else (puts Id.run do on same line)
fn render_branch<W: Write>(branch: &IRNode, need_monadic: bool, ctx: &mut RenderCtx<W>) {
    let stmts = branch.get_block_stmts();
    let result = branch.get_block_result();

    // Empty block
    if branch.is_unit() && stmts.is_empty() {
        ctx.write("sorry");
        return;
    }

    // Simple block - just result
    if stmts.is_empty() {
        render_simple_result(result, need_monadic, ctx);
        return;
    }

    // Block with statements - determine if monadic
    let has_monadic = need_monadic
        || stmts.iter().any(|s| s.contains_monadic(&|fid| ctx.is_func_monadic(fid)))
        || result.contains_monadic(&|fid| ctx.is_func_monadic(fid));

    // Optimize: pure block with single let where result is the bound variable
    if !has_monadic && stmts.len() == 1 {
        if let IRNode::Let { pattern, value, .. } = &stmts[0] {
            if pattern.len() == 1 {
                if let IRNode::Var(result_var) = result {
                    if &pattern[0] == result_var {
                        render(value, ctx);
                        return;
                    }
                }
            }
        }
    }

    // For branches, always use do-notation on the same line
    ctx.write(do_prefix(has_monadic));
    ctx.newline();
    ctx.indent();

    for (i, stmt) in stmts.iter().enumerate() {
        render_stmt_with_context(stmt, has_monadic, ctx);
        if i < stmts.len() - 1 {
            ctx.newline();
        }
    }

    ctx.newline();
    render_result(result, has_monadic, ctx);
    ctx.dedent();
}

/// Render a branch in a monadic if-expression, adding pure if needed
fn render_monadic_branch<W: Write>(branch: &IRNode, ctx: &mut RenderCtx<W>) {
    // If the branch is already monadic, just render it
    if branch.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
        render_branch(branch, true, ctx);
    } else {
        // Non-monadic branch - need to wrap the result in pure
        ctx.write("pure ");
        render_parens(branch, ctx);
    }
}

fn render_else_chain<W: Write>(else_branch: &IRNode, need_monadic: bool, ctx: &mut RenderCtx<W>) {
    // Check for else-if pattern
    if let IRNode::Block { children } = else_branch {
        if children.len() == 1 {
            if let IRNode::If {
                cond,
                then_branch,
                else_branch: nested_else,
            } = &children[0]
            {
                let cond_str = render_with_arrow_to_string(cond, ctx);
                ctx.write(&format!("\nelse if {} then ", cond_str));

                if need_monadic {
                    render_monadic_branch(then_branch, ctx);
                } else {
                    render_branch(then_branch, need_monadic, ctx);
                }

                render_else_chain(nested_else, need_monadic, ctx);
                return;
            }
        }
    }

    // Regular else
    ctx.write("\nelse ");
    if need_monadic {
        render_monadic_branch(else_branch, ctx);
    } else {
        render_branch(else_branch, need_monadic, ctx);
    }
}

fn render_return_if<W: Write>(
    cond: &IRNode,
    then_branch: &IRNode,
    else_branch: &IRNode,
    ctx: &mut RenderCtx<W>,
) {
    // Check if condition contains monadic operations
    let cond_has_monadic = cond.contains_monadic(&|fid| ctx.is_func_monadic(fid));

    if cond_has_monadic {
        // Need to bind condition in a do-block
        // The condition itself may not be monadic, but contains monadic subexpressions
        ctx.write("do\n");
        ctx.indent();
        ctx.write("let __cond := ");
        render(cond, ctx);
        ctx.newline();
        ctx.write("if decide __cond then");
    } else {
        let cond_str = render_to_string(cond, ctx);
        ctx.write(&format!("if {} then", cond_str));
    }
    ctx.newline();

    ctx.indent();
    render_block(then_branch, true, ctx);
    ctx.dedent();

    render_else_chain(else_branch, true, ctx);

    if cond_has_monadic {
        ctx.dedent();
    }
}

// ============================================================================
// While Loops
// ============================================================================

fn render_while_stmt<W: Write>(
    pattern: Option<&[String]>,
    cond: &IRNode,
    body: &IRNode,
    vars: &[String],
    ctx: &mut RenderCtx<W>,
) {
    let has_monadic = cond.contains_monadic(&|fid| ctx.is_func_monadic(fid))
        || body.contains_monadic(&|fid| ctx.is_func_monadic(fid));

    // Try to use native Lean while syntax when possible
    if try_render_native_while(pattern, cond, body, vars, has_monadic, ctx) {
        return;
    }

    // Fall back to whileLoopPure/whileLoop
    render_while_with_helper(pattern, cond, body, vars, has_monadic, ctx);
}

/// Attempt to render using Lean's native while syntax with mutable variables
fn try_render_native_while<W: Write>(
    pattern: Option<&[String]>,
    cond: &IRNode,
    body: &IRNode,
    vars: &[String],
    has_monadic: bool,
    ctx: &mut RenderCtx<W>,
) -> bool {
    // Only use native while for simple pure cases
    let cond_stmts = cond.get_block_stmts();
    if !cond_stmts.is_empty() || has_monadic {
        // Complex condition or monadic - fall back
        return false;
    }

    // Filter out temporary variables and deduplicate
    let mut seen = std::collections::HashSet::new();
    let real_vars: Vec<&String> = vars
        .iter()
        .filter(|v| !v.starts_with("$t") && seen.insert(*v))
        .collect();
    if real_vars.is_empty() {
        return false;
    }

    // Use do block with mutable variables
    ctx.write("do");
    ctx.newline();
    ctx.indent();

    // Initialize mutable variables from current scope
    for var in &real_vars {
        let escaped = crate::escape::escape_identifier(var);
        ctx.write(&format!("let mut {} := {}", escaped, escaped));
        ctx.newline();
    }

    // Render while loop with condition
    let cond_result = cond.get_block_result();
    ctx.write("while ");
    render(cond_result, ctx);
    ctx.write(" do");
    ctx.newline();
    ctx.indent();

    // Render body statements - convert let bindings to mutations
    let body_stmts = body.get_block_stmts();
    for (i, stmt) in body_stmts.iter().enumerate() {
        if let IRNode::Let { pattern, value, .. } = stmt {
            if pattern.len() == 1 {
                let var_name = &pattern[0];
                if vars.contains(var_name) {
                    // This is updating a loop variable - use mutation
                    let escaped = crate::escape::escape_identifier(var_name);
                    ctx.write(&format!("{} := ", escaped));
                    render(value, ctx);
                    if i < body_stmts.len() - 1 {
                        ctx.newline();
                    }
                    continue;
                }
            }
        }
        // Otherwise render normally
        render_stmt_with_context(stmt, false, ctx);
        if i < body_stmts.len() - 1 {
            ctx.newline();
        }
    }

    ctx.dedent();

    // Mutable variables are already in scope after the loop
    // No need to extract or rebind

    ctx.dedent();

    true
}

/// Render while using whileLoopPure/whileLoop helper functions
fn render_while_with_helper<W: Write>(
    pattern: Option<&[String]>,
    cond: &IRNode,
    body: &IRNode,
    vars: &[String],
    has_monadic: bool,
    ctx: &mut RenderCtx<W>,
) {
    let pattern_str = pattern.map(make_pattern).unwrap_or_else(|| make_pattern(vars));
    let state_pattern = make_pattern(vars);

    let init_str = render_tuple_like(vars, "()", ", ", |v| {
        if v.starts_with("$t") {
            "default".to_string()
        } else {
            crate::escape::escape_identifier(v)
        }
    });

    let (op, loop_fn) = if has_monadic {
        ("←", "whileLoop")
    } else {
        (":=", "whileLoopPure")
    };

    ctx.write(&format!(
        "let {} {} ({} (fun {} =>",
        pattern_str, op, loop_fn, state_pattern
    ));
    ctx.newline();
    ctx.indent();

    // For pure loops, don't use do blocks - just render the expression
    if !has_monadic {
        render_block_stmts(cond, ctx);
        let cond_result = cond.get_block_result();
        render(cond_result, ctx);
    } else {
        // For monadic loops, check if condition has statements
        let cond_stmts = cond.get_block_stmts();
        if cond_stmts.is_empty() {
            // No statements, just render the result wrapped in pure
            let cond_result = cond.get_block_result();
            render_result(cond_result, true, ctx);
        } else {
            // Has statements, need do-block
            ctx.write("do\n");
            ctx.indent();
            render_block_stmts(cond, ctx);
            let cond_result = cond.get_block_result();
            render_result(cond_result, true, ctx);
            ctx.dedent();
        }
    }

    ctx.dedent();
    ctx.write(&format!(") (fun {} =>", state_pattern));
    ctx.newline();
    ctx.indent();

    if !has_monadic {
        let body_stmts = body.get_block_stmts();
        if !body_stmts.is_empty() {
            render_block_stmts(body, ctx);
        }
        let return_tuple = var_tuple(vars);
        render(&return_tuple, ctx);
    } else {
        // For monadic loops, check if body has statements
        let body_stmts = body.get_block_stmts();
        let return_tuple = var_tuple(vars);

        if body_stmts.is_empty() {
            // No statements, just return the tuple wrapped in pure
            render_result(&return_tuple, true, ctx);
        } else {
            // Has statements, need do-block
            ctx.write("do\n");
            ctx.indent();
            render_block_stmts(body, ctx);
            render_result(&return_tuple, true, ctx);
            ctx.dedent();
        }
    }

    ctx.dedent();
    ctx.write(&format!(") {})", init_str));
}

// ============================================================================
// Blocks
// ============================================================================

pub fn render_block<W: Write>(ir: &IRNode, need_monadic: bool, ctx: &mut RenderCtx<W>) {
    let stmts = ir.get_block_stmts();
    let result = ir.get_block_result();

    // Empty block
    if ir.is_unit() && stmts.is_empty() {
        ctx.write("sorry");
        return;
    }

    // Simple block - just result
    if stmts.is_empty() {
        render_simple_result(result, need_monadic, ctx);
        return;
    }

    // Block with statements
    let has_monadic = need_monadic
        || stmts
            .iter()
            .any(|s| s.contains_monadic(&|fid| ctx.is_func_monadic(fid)))
        || result.contains_monadic(&|fid| ctx.is_func_monadic(fid));

    // Optimize: pure block with single let where result is the bound variable
    // Pattern: Id.run do let x := val; x  ->  val
    if !has_monadic && stmts.len() == 1 {
        if let IRNode::Let { pattern, value, .. } = &stmts[0] {
            if pattern.len() == 1 {
                if let IRNode::Var(result_var) = result {
                    if &pattern[0] == result_var {
                        // Just render the value directly
                        render(value, ctx);
                        return;
                    }
                }
            }
        }
    }

    // For pure blocks, use let-in syntax at top level (no Id.run do)
    // For branches or monadic blocks, use do-notation
    if !has_monadic && ctx.is_inline() == false {
        // Check if this is likely a function body (indentation level 1)
        // by seeing if we're not deeply nested
        // For now, always use semicolon syntax for pure blocks
        for stmt in stmts {
            render_stmt_with_context(stmt, false, ctx);
            ctx.write(";");
            ctx.newline();
        }
        render_result(result, false, ctx);
    } else {
        ctx.write(do_prefix(has_monadic));
        ctx.newline();
        ctx.indent();

        for (i, stmt) in stmts.iter().enumerate() {
            render_stmt_with_context(stmt, has_monadic, ctx);
            if i < stmts.len() - 1 {
                ctx.newline();
            }
        }

        ctx.newline();
        render_result(result, has_monadic, ctx);
        ctx.dedent();
    }
}

fn render_block_stmts<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    for stmt in ir.get_block_stmts() {
        render_stmt(stmt, ctx);
        ctx.newline();
    }
}

fn render_simple_result<W: Write>(result: &IRNode, need_monadic: bool, ctx: &mut RenderCtx<W>) {
    // Check if result is a complex statement that needs do block
    let is_complex_let = matches!(result, IRNode::Let { value, .. }
        if matches!(value.as_ref(), IRNode::If { .. } | IRNode::While { .. } | IRNode::Block { .. }));

    // Special handling for If/While in monadic context - render them directly
    if need_monadic {
        match result {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Check if condition contains monadic operations
                let cond_has_monadic = cond.contains_monadic(&|fid| ctx.is_func_monadic(fid));

                if cond_has_monadic {
                    ctx.write("do\n");
                    ctx.indent();
                    ctx.write("let __cond := ");
                    render(cond, ctx);
                    ctx.newline();
                    ctx.write("if decide __cond then");
                } else {
                    let cond_str = render_to_string(cond, ctx);
                    ctx.write(&format!("if {} then", cond_str));
                }
                ctx.newline();
                ctx.indent();
                render_monadic_branch(then_branch, ctx);
                ctx.dedent();
                render_else_chain(else_branch, true, ctx);
                if cond_has_monadic {
                    ctx.dedent();
                }
                return;
            }
            IRNode::While { cond, body, vars } => {
                render_while_stmt(None, cond, body, vars, ctx);
                return;
            }
            _ if is_complex_let => {
                let has_monadic = result.contains_monadic(&|fid| ctx.is_func_monadic(fid));
                ctx.write(do_prefix(has_monadic));
                ctx.newline();
                ctx.indent();
                render_stmt_with_context(result, has_monadic, ctx);
                ctx.dedent();
                return;
            }
            _ => {}
        }
    } else if is_complex_let {
        ctx.write("Id.run do\n");
        ctx.indent();
        render_stmt_with_context(result, false, ctx);
        ctx.dedent();
        return;
    }

    // Check if result has monadic subexpressions
    if need_monadic
        && result.contains_monadic(&|fid| ctx.is_func_monadic(fid))
        && !result.is_monadic(&|fid| ctx.is_func_monadic(fid))
    {
        ctx.write("do\n");
        ctx.indent();
        render_result(result, true, ctx);
        ctx.dedent();
        return;
    }

    render_result(result, need_monadic, ctx);
}

fn render_result<W: Write>(result: &IRNode, need_monadic: bool, ctx: &mut RenderCtx<W>) {
    // Special handling for if/while in monadic context - they need proper branch wrapping
    if need_monadic {
        match result {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                // Check if condition contains monadic operations
                let cond_has_monadic = cond.contains_monadic(&|fid| ctx.is_func_monadic(fid));

                if cond_has_monadic {
                    ctx.write("do\n");
                    ctx.indent();
                    ctx.write("let __cond := ");
                    render(cond, ctx);
                    ctx.newline();
                    ctx.write("if decide __cond then");
                } else {
                    let cond_str = render_to_string(cond, ctx);
                    ctx.write(&format!("if {} then", cond_str));
                }
                ctx.newline();

                ctx.indent();
                render_block(then_branch, true, ctx);
                ctx.dedent();

                render_else_chain(else_branch, true, ctx);
                if cond_has_monadic {
                    ctx.dedent();
                }
                return;
            }
            _ => {}
        }
    }

    if result.terminates() {
        render_stmt_with_context(result, need_monadic, ctx);
    } else if result.is_monadic(&|fid| ctx.is_func_monadic(fid)) {
        render(result, ctx);
    } else if need_monadic {
        ctx.write("pure ");
        render_parens(result, ctx);
    } else {
        render(result, ctx);
    }
}
