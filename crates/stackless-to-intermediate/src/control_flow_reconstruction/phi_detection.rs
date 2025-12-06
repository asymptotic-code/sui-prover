// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Phi Detection - Extracts phi variables from if/while expressions
//!
//! After structure discovery, we have if-expressions where both branches may assign
//! to the same variable. This pass detects those "phi" variables and restructures
//! the code so the if-expression returns those values.
//!
//! Key insight: phi detection only applies when BOTH branches continue (don't terminate).
//! When one branch terminates (Return/Abort), the if is a control flow statement,
//! not an expression, and no phi vars are needed.

use intermediate_theorem_format::IRNode;
use std::collections::BTreeSet;

/// Run phi detection on the entire IR tree
pub fn detect_phis(ir: IRNode) -> IRNode {
    transform_node(ir, &BTreeSet::new())
}

fn transform_node(ir: IRNode, vars_in_scope: &BTreeSet<String>) -> IRNode {
    match ir {
        IRNode::Block { children } => IRNode::Block {
            children: transform_block(children, vars_in_scope),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_branch = Box::new(transform_node(*then_branch, vars_in_scope));
            let else_branch = Box::new(transform_node(*else_branch, vars_in_scope));
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        IRNode::While {
            cond,
            body,
            vars: _,
        } => {
            // Apply while transformation even when While appears outside of transform_block
            let cond = transform_node(*cond, vars_in_scope);
            let body = transform_node(*body, vars_in_scope);
            // vars will be set by transform_while_in_block, but we pass through the existing value
            // in case this is already a transformed while
            transform_while_in_block(cond, body, vars_in_scope)
        }
        IRNode::Let { pattern, value } => {
            // Don't extend scope here - let bindings are only visible in their block,
            // not to nested blocks in their value expression
            IRNode::Let {
                pattern,
                value: Box::new(transform_node(*value, vars_in_scope)),
            }
        }
        other => other,
    }
}

fn transform_block(children: Vec<IRNode>, inherited_vars: &BTreeSet<String>) -> Vec<IRNode> {
    let mut result = Vec::new();
    // Track variables in scope: inherited from parent + defined so far in this block
    let mut vars_in_scope: BTreeSet<String> = inherited_vars.clone();

    for child in children {
        match child {
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let then_branch = transform_node(*then_branch, &vars_in_scope);
                let else_branch = transform_node(*else_branch, &vars_in_scope);
                let transformed =
                    transform_if_in_block(cond, then_branch, else_branch, &vars_in_scope);
                // Update vars_in_scope with any new bindings from the transformed if
                if let IRNode::Let { pattern, .. } = &transformed {
                    vars_in_scope.extend(pattern.iter().cloned());
                }
                result.push(transformed);
            }
            IRNode::While { cond, body, .. } => {
                let cond = transform_node(*cond, &vars_in_scope);
                let body = transform_node(*body, &vars_in_scope);
                let transformed = transform_while_in_block(cond, body, &vars_in_scope);
                // Update vars_in_scope with any new bindings from the transformed while
                if let IRNode::Let { pattern, .. } = &transformed {
                    vars_in_scope.extend(pattern.iter().cloned());
                }
                result.push(transformed);
            }
            other => {
                // Track let bindings
                if let IRNode::Let { pattern, .. } = &other {
                    vars_in_scope.extend(pattern.iter().cloned());
                }
                result.push(transform_node(other, &vars_in_scope));
            }
        }
    }

    result
}

fn transform_if_in_block(
    cond: Box<IRNode>,
    then_branch: IRNode,
    else_branch: IRNode,
    vars_in_scope: &BTreeSet<String>,
) -> IRNode {
    let then_terminates = then_branch.terminates();
    let else_terminates = else_branch.terminates();

    // If BOTH branches terminate, no phi detection needed
    if then_terminates && else_terminates {
        return IRNode::If {
            cond,
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        };
    }

    // If one branch terminates and the other doesn't, the non-terminating branch
    // may define variables that are used after the if. We need to make the if
    // expression return those variables so they're in scope after.
    if then_terminates || else_terminates {
        let (continuing_branch, terminating_branch, cond, swap_branches) = if else_terminates {
            (then_branch, else_branch, cond, false)
        } else {
            // then terminates, else continues - we'll negate the condition conceptually
            // by swapping branches in the final If
            (else_branch, then_branch, cond, true)
        };

        // Get variables defined in the continuing branch
        let continuing_vars: Vec<String> = collect_top_level_let_names(&continuing_branch)
            .into_iter()
            .collect();

        if continuing_vars.is_empty() {
            // No variables to lift - return as-is
            return if swap_branches {
                IRNode::If {
                    cond,
                    then_branch: Box::new(terminating_branch),
                    else_branch: Box::new(continuing_branch),
                }
            } else {
                IRNode::If {
                    cond,
                    then_branch: Box::new(continuing_branch),
                    else_branch: Box::new(terminating_branch),
                }
            };
        }

        // Add result expression to continuing branch
        let result_expr = if continuing_vars.len() == 1 {
            IRNode::Var(continuing_vars[0].clone())
        } else {
            IRNode::Tuple(continuing_vars.iter().map(|n| IRNode::Var(n.clone())).collect())
        };

        let continuing_with_result = match continuing_branch {
            IRNode::Block { mut children } => {
                children.push(result_expr);
                IRNode::Block { children }
            }
            other => IRNode::Block {
                children: vec![other, result_expr],
            },
        };

        // Wrap in let binding
        let if_expr = if swap_branches {
            IRNode::If {
                cond,
                then_branch: Box::new(terminating_branch),
                else_branch: Box::new(continuing_with_result),
            }
        } else {
            IRNode::If {
                cond,
                then_branch: Box::new(continuing_with_result),
                else_branch: Box::new(terminating_branch),
            }
        };

        return IRNode::Let {
            pattern: continuing_vars,
            value: Box::new(if_expr),
        };
    }

    // Both branches continue - find variables assigned in each branch
    let then_vars = collect_top_level_let_names(&then_branch);
    let else_vars = collect_top_level_let_names(&else_branch);

    // Case 1: Variables assigned in both branches (standard phi)
    let common_vars: BTreeSet<String> = then_vars.intersection(&else_vars).cloned().collect();

    // Case 2: Variables assigned only in one branch BUT that existed before the if
    // These are single-arm mutations: if (cond) { x = newval; } where x was defined before
    let then_only: BTreeSet<String> = then_vars.difference(&else_vars).cloned().collect();
    let else_only: BTreeSet<String> = else_vars.difference(&then_vars).cloned().collect();

    // Only include single-arm vars if they were in scope before the if
    let then_only_in_scope: Vec<String> = then_only.intersection(vars_in_scope).cloned().collect();
    let else_only_in_scope: Vec<String> = else_only.intersection(vars_in_scope).cloned().collect();

    // Combine: common vars + single-arm mutations of pre-existing vars
    let mut phi_vars: Vec<String> = common_vars.into_iter().collect();
    phi_vars.extend(then_only_in_scope.iter().cloned());
    phi_vars.extend(else_only_in_scope.iter().cloned());
    phi_vars.sort(); // Ensure consistent ordering

    if phi_vars.is_empty() {
        return IRNode::If {
            cond,
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        };
    }

    // Build if-expression that returns phi values
    // For single-arm mutations, the branch without the assignment passes through the old value
    let then_result = append_result_with_passthrough(then_branch, &phi_vars, &else_only_in_scope);
    let else_result = append_result_with_passthrough(else_branch, &phi_vars, &then_only_in_scope);

    IRNode::Let {
        pattern: phi_vars,
        value: Box::new(IRNode::If {
            cond,
            then_branch: Box::new(then_result),
            else_branch: Box::new(else_result),
        }),
    }
}

/// Transform a while loop to properly track loop-modified state variables.
///
/// A while loop modifies variables across iterations. We need to:
/// 1. Find variables assigned in the loop body that existed before the loop
/// 2. Make the loop return those variables as a tuple
/// 3. Bind the result to those variables after the loop
///
/// Only variables that were in scope before the while loop are included,
/// since the initial state tuple must reference values that already exist.
fn transform_while_in_block(
    cond: IRNode,
    body: IRNode,
    vars_in_scope: &BTreeSet<String>,
) -> IRNode {
    // Collect variables assigned in the body that were defined before the loop
    let body_assigned = collect_top_level_let_names(&body);

    // Find variables that are both assigned in the body AND existed before the loop.
    // This includes temps (starting with $t) which will be optimized away later.
    let loop_vars: Vec<String> = body_assigned.intersection(vars_in_scope).cloned().collect();

    if loop_vars.is_empty() {
        // No pre-existing variables modified - loop doesn't need state tracking
        return IRNode::While {
            cond: Box::new(cond),
            body: Box::new(body),
            vars: vec![],
        };
    }

    // Wrap while in a let binding that captures the final state
    IRNode::Let {
        pattern: loop_vars.clone(),
        value: Box::new(IRNode::While {
            cond: Box::new(cond),
            body: Box::new(body),
            vars: loop_vars,
        }),
    }
}

/// Collect names of let bindings at the top level of a block
fn collect_top_level_let_names(ir: &IRNode) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    match ir {
        IRNode::Block { children } => {
            for child in children {
                if let IRNode::Let { pattern, .. } = child {
                    for name in pattern {
                        vars.insert(name.clone());
                    }
                }
            }
        }
        IRNode::Let { pattern, .. } => {
            for name in pattern {
                vars.insert(name.clone());
            }
        }
        _ => {}
    }
    vars
}

/// Append result expression with passthrough for variables not assigned in this branch.
/// `passthrough_vars` are variables that this branch doesn't assign but are part of phi_vars.
/// We need to reference the old value (which is in scope from before the if).
fn append_result_with_passthrough(
    ir: IRNode,
    phi_vars: &[String],
    passthrough_vars: &[String],
) -> IRNode {
    let result_expr = match phi_vars.len() {
        1 => IRNode::Var(phi_vars[0].clone()),
        _ => IRNode::Tuple(
            phi_vars
                .iter()
                .map(|name| IRNode::Var(name.clone()))
                .collect(),
        ),
    };

    // For passthrough vars, we need to add a let binding that shadows the old value with itself.
    // This ensures the variable name exists in this branch's scope for the result tuple.
    // e.g., if then-branch assigns ratio_1_0 but else-branch doesn't:
    //   else: let ratio_1_0 := ratio_1_0; (ratio_1_0)
    let passthrough_bindings: Vec<IRNode> = passthrough_vars
        .iter()
        .map(|name| IRNode::Let {
            pattern: vec![name.clone()],
            value: Box::new(IRNode::Var(name.clone())),
        })
        .collect();

    match ir {
        IRNode::Block { mut children } => {
            children.extend(passthrough_bindings);
            children.push(result_expr);
            IRNode::Block { children }
        }
        other => {
            let mut children = vec![other];
            children.extend(passthrough_bindings);
            children.push(result_expr);
            IRNode::Block { children }
        }
    }
}
