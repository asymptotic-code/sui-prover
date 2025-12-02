// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Cleanup pass for TheoremIR
//!
//! Transformations:
//! 1. Remove identity assignments: `let x := x` -> removed
//! 2. Copy propagation: `let tmp := expr; let x := tmp` -> `let x := expr`

use crate::IRNode;
use std::collections::BTreeMap;

pub fn cleanup(node: IRNode) -> IRNode {
    node.transform_block(|children| {
        apply_copy_propagation(
            children
                .into_iter()
                .filter(|c| !is_identity_let(c))
                .collect(),
        )
    })
}

fn apply_copy_propagation(nodes: Vec<IRNode>) -> Vec<IRNode> {
    // Find copy patterns: `let x = expr; let y = x` -> remove `let y = x`, substitute y → x
    let (indices_to_remove, subs): (Vec<usize>, BTreeMap<String, String>) = nodes
        .windows(2)
        .enumerate()
        .filter_map(|(index, window)| {
            // Returns (original_name, copy_name) - we want to replace copy_name with original_name
            try_propagate(&window[0], &window[1]).map(|(orig, copy)| (index + 1, (copy, orig)))
        })
        .unzip();

    nodes
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !indices_to_remove.contains(i))
        .map(|(_, node)| node.substitute_vars(&subs))
        .collect()
}

/// Detects `let x = expr; let y = x` pattern, returns (original_name, copy_name)
fn try_propagate(first: &IRNode, second: &IRNode) -> Option<(String, String)> {
    let (def_name, _) = single_pattern_let(first)?;
    let (copy_name, IRNode::Var(use_value)) = single_pattern_let(second)? else {
        return None;
    };
    if use_value != def_name {
        return None;
    }
    Some((def_name.clone(), copy_name.clone()))
}

fn is_identity_let(ir: &IRNode) -> bool {
    single_pattern_let(ir)
        .map(|(name, value)| matches!(value, IRNode::Var(v) if v == name))
        .unwrap_or(false)
}

fn single_pattern_let(ir: &IRNode) -> Option<(&String, &IRNode)> {
    ir.destructure_let()
        .filter(|(pattern, _)| pattern.len() == 1)
        .map(|(pattern, value)| (&pattern[0], value.as_ref()))
}
