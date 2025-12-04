// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Cleanup pass for TheoremIR
//!
//! Transformations:
//! 1. Remove identity assignments: `let x := x` -> removed
//! 2. Simplify boolean if expressions: `if cond then true else false` -> `cond`

use crate::{Const, IRNode};

pub fn cleanup(node: IRNode) -> IRNode {
    let node = node.transform_block(|children| {
        children
            .into_iter()
            .filter(|c| !is_identity_let(c))
            .collect()
    });

    // Apply boolean simplification after other cleanups
    simplify_boolean_ifs(node)
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
