// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Dead code removal pass
//!
//! Removes Let statements where the bound variables are never used.
//! Preserves side-effecting expressions (function calls, etc.) even if unused.

use crate::IRNode;
use std::collections::BTreeSet;

pub fn remove_dead_code(ir: IRNode) -> IRNode {
    let used: BTreeSet<String> = ir.used_vars().cloned().collect();
    ir.transform_block(|children| children.into_iter().filter(|c| !is_dead_let(c, &used)).collect())
}

fn is_dead_let(ir: &IRNode, used: &BTreeSet<String>) -> bool {
    let Some((pattern, value)) = ir.destructure_let() else {
        return false;
    };
    // Only remove Let bindings where:
    // 1. None of the pattern variables are used
    // 2. The value has no side effects (no function calls that could abort or mutate)
    // For now, conservatively: only remove pure expressions
    pattern.iter().all(|n| !used.contains(n)) && is_pure(value)
}

/// Check if an expression is pure (no side effects)
fn is_pure(ir: &IRNode) -> bool {
    match ir {
        IRNode::Var(_) | IRNode::Const(_) => true,
        IRNode::BinOp { lhs, rhs, .. } => is_pure(lhs) && is_pure(rhs),
        IRNode::UnOp { operand, .. } => is_pure(operand),
        IRNode::Tuple(elems) => elems.iter().all(is_pure),
        IRNode::Field { base, .. } => is_pure(base),
        // Everything else potentially has side effects
        _ => false,
    }
}
