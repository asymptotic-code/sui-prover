// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Functional helpers for common rendering patterns

use intermediate_theorem_format::IRNode;

/// Construct a variable tuple from names
pub fn var_tuple(vars: &[String]) -> IRNode {
    match vars {
        [] => IRNode::Tuple(vec![]),
        [single] => IRNode::Var(single.clone()),
        multiple => IRNode::Tuple(multiple.iter().map(|v| IRNode::Var(v.clone())).collect()),
    }
}
