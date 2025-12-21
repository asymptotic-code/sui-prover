// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Monadicity analysis pass
//!
//! All functions start as monadic (return type wrapped in Except).
//! This pass identifies pure functions and unwraps their return types.
//!
//! Prerequisites: DependencyOrderPass must have run first.
//! Prerequisites: Base functions should be optimized first for best results.

use crate::data::Program;
use crate::{FunctionID, IRNode, Const, BinOp};
use std::collections::BTreeSet;

pub fn analyze_monadicity(program: &mut Program) {
    let func_ids: Vec<_> = program.functions.iter_ids().collect();

    // First pass: identify which functions have intrinsic abort nodes
    let mut has_abort: BTreeSet<FunctionID> = BTreeSet::new();
    for func_id in &func_ids {
        let func = program.functions.get(func_id);
        if func.body.aborts() {
            has_abort.insert(*func_id);
        }
    }
    let has_abort_bases: std::collections::HashSet<usize> = has_abort.iter().map(|id| id.base).collect();

    // Second pass: compute abort predicates and determine true monadicity
    // A function is monadic only if its abort predicate doesn't simplify to False
    // Process in dependency order - functions are already sorted
    let mut monadic_funcs: BTreeSet<FunctionID> = BTreeSet::new();

    for func_id in &func_ids {
        let func = program.functions.get(func_id);
        if func.is_native() {
            log::debug!("[MONADICITY] {} -> skipped (native)", func.name);
            continue;
        }
        if func.is_spec() {
            log::debug!("[MONADICITY] {} -> skipped (spec)", func.name);
            continue;
        }

        // Compute full abort predicate (handles both intrinsic aborts and calls)
        let monadic_bases: std::collections::HashSet<usize> = monadic_funcs.iter().map(|id| id.base).collect();
        let abort_pred = compute_full_abort_predicate(&func.body, &has_abort_bases, &monadic_bases, program);
        let simplified = crate::analysis::logical_simplify(abort_pred);

        let is_monadic = !matches!(simplified, IRNode::Const(Const::Bool(false)));
        log::debug!("[MONADICITY] {} -> {:?} -> is_monadic={}", func.name, simplified, is_monadic);
        if is_monadic {
            monadic_funcs.insert(*func_id);
        }
    }

    // Collect monadic base IDs for call rewriting
    let monadic_base_ids: BTreeSet<usize> = monadic_funcs.iter().map(|id| id.base).collect();

    // Third pass: unwrap return types for non-monadic functions
    // Also rewrite calls to monadic functions to use .pure variant
    for func_id in &func_ids {
        if !monadic_funcs.contains(func_id) {
            let func = program.functions.get_mut(*func_id);
            if let Some(inner) = func.signature.return_type.unwrap_monad().cloned() {
                func.signature.return_type = inner;
            }
            // Rewrite calls to monadic functions to use .pure variant
            let body = std::mem::replace(&mut func.body, IRNode::Tuple(vec![]));
            func.body = body.to_variant(crate::FunctionVariant::Pure, |base| {
                monadic_base_ids.contains(&base)
            });
        }
    }
}

/// Compute full abort predicate for a function body.
/// Handles both intrinsic aborts and calls to monadic functions.
fn compute_full_abort_predicate(
    body: &IRNode,
    has_abort_bases: &std::collections::HashSet<usize>,
    monadic_bases: &std::collections::HashSet<usize>,
    program: &Program,
) -> IRNode {
    let mut visited = std::collections::HashSet::new();
    compute_full_abort_predicate_impl(body, has_abort_bases, monadic_bases, program, &mut visited)
}

/// Implementation with cycle detection
fn compute_full_abort_predicate_impl(
    body: &IRNode,
    has_abort_bases: &std::collections::HashSet<usize>,
    monadic_bases: &std::collections::HashSet<usize>,
    program: &Program,
    visited: &mut std::collections::HashSet<usize>,
) -> IRNode {
    // Convert Abort nodes to True
    let converted = body.clone().map(&mut |n| match n {
        IRNode::Abort(_) => IRNode::Const(Const::Bool(true)),
        other => other,
    });

    // Extract abort conditions from both intrinsic aborts and monadic calls
    extract_abort_condition_full(converted, has_abort_bases, monadic_bases, program, visited)
}

/// Extract abort condition handling both intrinsic True nodes and calls to monadic functions.
fn extract_abort_condition_full(
    node: IRNode,
    has_abort_bases: &std::collections::HashSet<usize>,
    monadic_bases: &std::collections::HashSet<usize>,
    program: &Program,
    visited: &mut std::collections::HashSet<usize>,
) -> IRNode {
    match node {
        // True means this path aborts (from converted Abort nodes)
        IRNode::Const(Const::Bool(true)) => IRNode::Const(Const::Bool(true)),
        IRNode::Const(Const::Bool(false)) => IRNode::Const(Const::Bool(false)),

        // Calls to monadic functions - inline the abort predicate
        IRNode::Call { function, args, type_args: _ } if monadic_bases.contains(&function.base) => {
            // Check for cycles to prevent infinite recursion
            if visited.contains(&function.base) {
                // Conservative: assume function might abort if we're in a cycle
                return IRNode::Const(Const::Bool(true));
            }

            visited.insert(function.base);

            // Get the callee's abort predicate and substitute args
            let callee = program.functions.get(&FunctionID::new(function.base));
            let callee_abort_pred = compute_full_abort_predicate_impl(
                &callee.body,
                has_abort_bases,
                monadic_bases,
                program,
                visited,
            );

            visited.remove(&function.base);

            // Substitute parameters with arguments
            let params: Vec<&str> = callee.signature.parameters.iter()
                .map(|p| p.name.as_str())
                .collect();
            substitute_params(callee_abort_pred, &params, &args)
        }

        // Return - check returned values
        IRNode::Return(values) => {
            let conditions: Vec<_> = values.into_iter()
                .map(|v| extract_abort_condition_full(v, has_abort_bases, monadic_bases, program, visited))
                .filter(|c| !matches!(c, IRNode::Const(Const::Bool(false))))
                .collect();
            or_conditions(conditions)
        }

        // Block - extract from all children
        IRNode::Block { children } => {
            let conditions: Vec<_> = children.into_iter()
                .map(|c| extract_abort_condition_full(c, has_abort_bases, monadic_bases, program, visited))
                .filter(|c| !matches!(c, IRNode::Const(Const::Bool(false))))
                .collect();
            or_conditions(conditions)
        }

        // Let - extract from value
        IRNode::Let { value, .. } => extract_abort_condition_full(*value, has_abort_bases, monadic_bases, program, visited),

        // While - check if condition or body can abort
        IRNode::While { cond, body, .. } => {
            let cond_abort = extract_abort_condition_full(*cond, has_abort_bases, monadic_bases, program, visited);
            let body_abort = extract_abort_condition_full(*body, has_abort_bases, monadic_bases, program, visited);

            let cond_is_false = matches!(cond_abort, IRNode::Const(Const::Bool(false)));
            let body_is_false = matches!(body_abort, IRNode::Const(Const::Bool(false)));

            if cond_is_false && body_is_false {
                IRNode::Const(Const::Bool(false))
            } else if cond_is_false {
                body_abort
            } else if body_is_false {
                cond_abort
            } else {
                IRNode::BinOp {
                    op: BinOp::Or,
                    lhs: Box::new(cond_abort),
                    rhs: Box::new(body_abort),
                }
            }
        }

        // If - properly guard branches with condition
        IRNode::If { cond, then_branch, else_branch } => {
            let then_abort = extract_abort_condition_full(*then_branch, has_abort_bases, monadic_bases, program, visited);
            let else_abort = extract_abort_condition_full(*else_branch, has_abort_bases, monadic_bases, program, visited);

            let then_is_false = matches!(then_abort, IRNode::Const(Const::Bool(false)));
            let else_is_false = matches!(else_abort, IRNode::Const(Const::Bool(false)));
            let then_is_true = matches!(then_abort, IRNode::Const(Const::Bool(true)));
            let else_is_true = matches!(else_abort, IRNode::Const(Const::Bool(true)));

            if then_is_false && else_is_false {
                IRNode::Const(Const::Bool(false))
            } else if then_is_true && else_is_true {
                IRNode::Const(Const::Bool(true))
            } else if else_is_false {
                if then_is_true {
                    *cond
                } else {
                    IRNode::BinOp {
                        op: BinOp::And,
                        lhs: cond,
                        rhs: Box::new(then_abort),
                    }
                }
            } else if then_is_false {
                let not_cond = IRNode::UnOp {
                    op: crate::UnOp::Not,
                    operand: cond,
                };
                if else_is_true {
                    not_cond
                } else {
                    IRNode::BinOp {
                        op: BinOp::And,
                        lhs: Box::new(not_cond),
                        rhs: Box::new(else_abort),
                    }
                }
            } else {
                let then_guarded = if then_is_true {
                    (*cond).clone()
                } else {
                    IRNode::BinOp {
                        op: BinOp::And,
                        lhs: cond.clone(),
                        rhs: Box::new(then_abort),
                    }
                };
                let not_cond = IRNode::UnOp {
                    op: crate::UnOp::Not,
                    operand: cond,
                };
                let else_guarded = if else_is_true {
                    not_cond
                } else {
                    IRNode::BinOp {
                        op: BinOp::And,
                        lhs: Box::new(not_cond),
                        rhs: Box::new(else_abort),
                    }
                };
                IRNode::BinOp {
                    op: BinOp::Or,
                    lhs: Box::new(then_guarded),
                    rhs: Box::new(else_guarded),
                }
            }
        }

        // Other nodes - no abort
        _ => IRNode::Const(Const::Bool(false)),
    }
}

/// OR together a list of conditions, returning False if empty
fn or_conditions(conditions: Vec<IRNode>) -> IRNode {
    if conditions.is_empty() {
        IRNode::Const(Const::Bool(false))
    } else if conditions.len() == 1 {
        conditions.into_iter().next().unwrap()
    } else {
        conditions.into_iter().reduce(|acc, c| IRNode::BinOp {
            op: BinOp::Or,
            lhs: Box::new(acc),
            rhs: Box::new(c),
        }).unwrap()
    }
}

/// Substitute parameter names with argument values in an IR node
fn substitute_params(node: IRNode, params: &[&str], args: &[IRNode]) -> IRNode {
    node.map(&mut |n| {
        if let IRNode::Var(name) = &n {
            if let Some(idx) = params.iter().position(|&p| p == name) {
                return args[idx].clone();
            }
        }
        n
    })
}
