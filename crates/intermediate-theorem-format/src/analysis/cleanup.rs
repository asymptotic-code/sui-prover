// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Cleanup pass for TheoremIR
//!
//! Transformations:
//! 1. Remove identity assignments: `let x := x` -> removed
//! 2. Simplify boolean if expressions: `if cond then true else false` -> `cond`
//! 3. Convert nested boolean ifs to AND: `if A then B else false` -> `A && B`

use crate::data::variables::TypeContext;
use crate::{BinOp, Const, IRNode, Type};

pub fn cleanup(node: IRNode, ctx: &TypeContext) -> IRNode {
    let node = node.filter(|n| !is_identity_let(n));
    let node = simplify_boolean_ifs(node);
    let node = convert_boolean_ifs_to_and(node, ctx);
    node
}

fn is_identity_let(ir: &IRNode) -> bool {
    single_pattern_let(ir)
        .map(|(name, value)| matches!(value, IRNode::Var(v) if v == name))
        .unwrap_or(false)
}

fn single_pattern_let(ir: &IRNode) -> Option<(&String, &IRNode)> {
    match ir {
        IRNode::Let { pattern, value } if pattern.len() == 1 => Some((&pattern[0], value.as_ref())),
        _ => None,
    }
}

/// Simplify boolean if expressions recursively
/// - `if cond then true else false` -> `cond`
/// - `if cond then false else true` -> `!cond`
fn simplify_boolean_ifs(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Check if both branches are boolean constants
            let then_is_true = matches!(*then_branch.as_ref(), IRNode::Const(Const::Bool(true)));
            let then_is_false = matches!(*then_branch.as_ref(), IRNode::Const(Const::Bool(false)));
            let else_is_true = matches!(*else_branch.as_ref(), IRNode::Const(Const::Bool(true)));
            let else_is_false = matches!(*else_branch.as_ref(), IRNode::Const(Const::Bool(false)));

            if then_is_true && else_is_false {
                // if cond then true else false -> cond
                *cond
            } else if then_is_false && else_is_true {
                // if cond then false else true -> !cond
                IRNode::UnOp {
                    op: crate::UnOp::Not,
                    operand: cond,
                }
            } else {
                // Keep as is
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
        }
        other => other,
    })
}

/// Convert nested boolean if patterns to AND operations
/// Pattern: `if cond1 then cond2 else false` -> `cond1 && cond2`
/// This handles the common case of short-circuit AND evaluation from Move's `&&` operator
fn convert_boolean_ifs_to_and(node: IRNode, ctx: &TypeContext) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Helper to get the effective value if it's a boolean constant (possibly wrapped in Block/Return)
            fn get_bool_const(node: &IRNode) -> Option<bool> {
                match node {
                    IRNode::Const(Const::Bool(b)) => Some(*b),
                    IRNode::Block { children } if children.len() == 1 => get_bool_const(&children[0]),
                    IRNode::Return(values) if values.len() == 1 => get_bool_const(&values[0]),
                    _ => None,
                }
            }

            // Check for both branches being the same boolean constant
            // if X then true else true => true, if X then false else false => false
            if let (Some(then_val), Some(else_val)) = (get_bool_const(&then_branch), get_bool_const(&else_branch)) {
                if then_val == else_val {
                    // Both branches same constant - return that constant
                    return IRNode::Const(Const::Bool(then_val));
                }
            }

            // Check if else branch is false
            let else_is_false = matches!(*else_branch.as_ref(), IRNode::Const(Const::Bool(false)));
            let then_is_false = matches!(*then_branch.as_ref(), IRNode::Const(Const::Bool(false)));

            // Don't convert if both are false (should be handled above, but double-check)
            if else_is_false && !then_is_false {
                // Check if then_branch is a boolean expression using type tracking
                if is_boolean_type(&then_branch, ctx) {
                    // Convert to AND operation: cond1 && cond2
                    IRNode::BinOp {
                        op: BinOp::And,
                        lhs: cond,
                        rhs: then_branch,
                    }
                } else {
                    // Keep as is
                    IRNode::If {
                        cond,
                        then_branch,
                        else_branch,
                    }
                }
            } else {
                // Keep as is
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
        }
        other => other,
    })
}

/// Check if an IR node has a boolean type using the full TypeContext
fn is_boolean_type(node: &IRNode, ctx: &TypeContext) -> bool {
    node.get_type(ctx)
        .map(|ty| matches!(ty, Type::Bool))
        .unwrap_or(false)
}
