// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Temp inlining pass
//!
//! Inlines generated temporaries (variables starting with $) using a simple
//! sequential forward substitution approach:
//!
//! 1. Process statements in order
//! 2. When we see `let $t = value`, substitute any known temps in `value`,
//!    store the result in our map, and remove the let
//! 3. When we see a variable reference to a known temp, replace it with the stored value
//!
//! This approach is safe because:
//! - We only substitute temps we've already seen (no forward references)
//! - Each temp's value is fully expanded when stored (no fixpoint needed)
//! - No recursion on definitions (just map lookup + tree substitution)

use crate::{IRNode, VariableRegistry};
use std::collections::BTreeMap;

/// Inline all temps in the given IR.
pub fn inline_temps(ir: IRNode, _registry: &VariableRegistry) -> IRNode {
    inline_in_node(ir, &BTreeMap::new())
}

/// Substitute known temps in an IR node (non-recursive on definitions)
fn substitute_temps(ir: IRNode, temps: &BTreeMap<String, IRNode>) -> IRNode {
    ir.transform(&mut |node| {
        if let IRNode::Var(name) = &node {
            if let Some(value) = temps.get(name) {
                return value.clone();
            }
        }
        node
    })
}

/// Process a node, inlining temps. `temps` contains temps defined in outer scopes.
fn inline_in_node(ir: IRNode, outer_temps: &BTreeMap<String, IRNode>) -> IRNode {
    match ir {
        IRNode::Block { children } => inline_block(children, outer_temps),
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Substitute temps in condition
            let cond = substitute_temps(*cond, outer_temps);
            // Process branches with outer temps (branches may define new temps locally)
            let then_branch = inline_in_node(*then_branch, outer_temps);
            let else_branch = inline_in_node(*else_branch, outer_temps);
            IRNode::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            }
        }
        IRNode::While { cond, body, vars } => {
            // For while loops, we need to be careful: temps assigned in the body
            // shouldn't be inlined since they change each iteration.
            // We only inline outer temps that aren't redefined in the loop.
            let loop_defined: Vec<String> = body.defined_vars().cloned().collect();
            let safe_temps: BTreeMap<String, IRNode> = outer_temps
                .iter()
                .filter(|(name, _)| !loop_defined.contains(name))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();

            let cond = inline_in_node(*cond, &safe_temps);
            let body = inline_in_node(*body, &safe_temps);

            // Remove any temps from the vars list that we've inlined
            let vars = vars
                .into_iter()
                .filter(|v| !outer_temps.contains_key(v))
                .collect();

            IRNode::While {
                cond: Box::new(cond),
                body: Box::new(body),
                vars,
            }
        }
        IRNode::Let { pattern, value } => {
            // Substitute temps in the value
            let value = substitute_temps(*value, outer_temps);
            // Pattern filtering for While is handled in inline_block
            IRNode::Let {
                pattern,
                value: Box::new(value),
            }
        }
        // For other nodes, just substitute temps in all children
        other => substitute_temps(other, outer_temps),
    }
}

/// Process a block sequentially, building up temp definitions as we go
fn inline_block(children: Vec<IRNode>, outer_temps: &BTreeMap<String, IRNode>) -> IRNode {
    let mut temps = outer_temps.clone();
    let mut result = Vec::new();

    for child in children {
        match child {
            IRNode::Let { pattern, value } if is_single_temp(&pattern) => {
                // This is a temp definition - substitute, store, and skip
                let value = inline_in_node(*value, &temps);
                temps.insert(pattern[0].clone(), value);
                // Don't emit this let - the temp is inlined
            }
            IRNode::Let { pattern, value } => {
                // Non-temp let - substitute temps in value and keep
                let value = inline_in_node(*value, &temps);

                // If the value is a While, filter the pattern to match the While's vars
                // (temps have been removed from the While's vars by inline_in_node)
                let pattern = if let IRNode::While { vars, .. } = &value {
                    // Only keep variables that are in the while's vars list
                    pattern.into_iter().filter(|v| vars.contains(v)).collect()
                } else {
                    pattern
                };

                result.push(IRNode::Let {
                    pattern,
                    value: Box::new(value),
                });
            }
            other => {
                // Process the node with current temps
                result.push(inline_in_node(other, &temps));
            }
        }
    }

    IRNode::Block { children: result }
}

/// Check if pattern is a single temp variable
fn is_single_temp(pattern: &[String]) -> bool {
    pattern.len() == 1 && VariableRegistry::is_temp(&pattern[0])
}
