// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Temp inlining pass
//!
//! Inlines all non-named temporaries (variables starting with $).
//! This is a simple substitution pass - every temp is inlined at its use sites.

use crate::{IRNode, VariableRegistry};
use std::collections::BTreeMap;

/// Inline all temps in the given IR.
pub fn inline_temps(ir: IRNode, _registry: &VariableRegistry) -> IRNode {
    inline_block(ir)
}

fn inline_block(ir: IRNode) -> IRNode {
    match ir {
        IRNode::Block { children } => {
            // Collect all temp definitions from Let nodes
            let mut definitions: BTreeMap<String, IRNode> = BTreeMap::new();
            for child in &children {
                if let IRNode::Let { pattern, value } = child {
                    if pattern.len() == 1 && VariableRegistry::is_temp(&pattern[0]) {
                        definitions.insert(pattern[0].clone(), value.as_ref().clone());
                    }
                }
            }

            // Expand definitions to get fully inlined values
            fixpoint_expand(&mut definitions);

            // Filter out temp Let nodes and inline in remaining
            let new_children: Vec<IRNode> = children
                .into_iter()
                .filter_map(|child| {
                    if let IRNode::Let { pattern, .. } = &child {
                        if pattern.len() == 1 && definitions.contains_key(&pattern[0]) {
                            return None;
                        }
                    }
                    Some(inline_in_node(child, &definitions))
                })
                .collect();

            IRNode::Block { children: new_children }
        }
        other => inline_in_node(other, &BTreeMap::new()),
    }
}

fn fixpoint_expand(definitions: &mut BTreeMap<String, IRNode>) {
    loop {
        let mut changed = false;
        let names: Vec<_> = definitions.keys().cloned().collect();
        for name in names {
            let expr = definitions.get(&name).unwrap().clone();
            let new_expr = substitute_temps(expr.clone(), definitions);
            if expr != new_expr {
                definitions.insert(name, new_expr);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

fn substitute_temps(ir: IRNode, definitions: &BTreeMap<String, IRNode>) -> IRNode {
    match &ir {
        IRNode::Var(name) if definitions.contains_key(name) => {
            definitions.get(name).unwrap().clone()
        }
        IRNode::If { .. } | IRNode::While { .. } | IRNode::Const(_) => ir,
        _ => ir.map(&mut |child| substitute_temps(child, definitions)),
    }
}

fn inline_in_node(ir: IRNode, definitions: &BTreeMap<String, IRNode>) -> IRNode {
    match ir {
        IRNode::Var(ref name) if definitions.contains_key(name) => {
            inline_in_node(definitions.get(name).unwrap().clone(), definitions)
        }
        IRNode::Let { pattern, value } => IRNode::Let {
            pattern,
            value: Box::new(inline_in_node(*value, definitions)),
        },
        IRNode::If { cond, then_branch, else_branch } => IRNode::If {
            cond: Box::new(inline_in_node(*cond, definitions)),
            then_branch: Box::new(inline_block_with(*then_branch, definitions)),
            else_branch: Box::new(inline_block_with(*else_branch, definitions)),
        },
        IRNode::While { cond, body } => {
            // In while loops, don't inline vars that are mutated in the body
            let loop_vars: Vec<String> = body.defined_vars().cloned().collect();
            let filtered: BTreeMap<String, IRNode> = definitions
                .iter()
                .filter(|(name, _)| !loop_vars.contains(name))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            IRNode::While {
                cond: Box::new(inline_block_with(*cond, &filtered)),
                body: Box::new(inline_block_with(*body, &filtered)),
            }
        }
        IRNode::Block { children } => {
            // Recursively process nested blocks
            inline_block(IRNode::Block { children })
        }
        _ => ir.map(&mut |child| inline_in_node(child, definitions)),
    }
}

fn inline_block_with(ir: IRNode, outer_definitions: &BTreeMap<String, IRNode>) -> IRNode {
    match ir {
        IRNode::Block { children } => {
            // Collect local temp definitions
            let mut definitions = outer_definitions.clone();
            for child in &children {
                if let IRNode::Let { pattern, value } = child {
                    if pattern.len() == 1 && VariableRegistry::is_temp(&pattern[0]) {
                        definitions.insert(pattern[0].clone(), value.as_ref().clone());
                    }
                }
            }

            fixpoint_expand(&mut definitions);

            let new_children: Vec<IRNode> = children
                .into_iter()
                .filter_map(|child| {
                    if let IRNode::Let { pattern, .. } = &child {
                        if pattern.len() == 1 && definitions.contains_key(&pattern[0]) {
                            return None;
                        }
                    }
                    Some(inline_in_node(child, &definitions))
                })
                .collect();

            IRNode::Block { children: new_children }
        }
        other => inline_in_node(other, outer_definitions),
    }
}
