// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates requires/ensures IR functions from spec functions.
//!
//! For functions marked with #[spec(prove)], this pass:
//! 1. Copies the function body
//! 2. Extracts IRNode::Requires and IRNode::Ensures calls
//! 3. Replaces the return with AND of all requires/ensures conditions
//! 4. Creates separate `.requires` and `.ensures` IR functions

use crate::data::functions::FunctionVariant;
use crate::data::Program;
use crate::{Const, IRNode, Type};

/// Recursively count occurrences of a specific IRNode type in the tree
fn count_nodes_recursive<F>(nodes: &[IRNode], pred: F) -> usize
where
    F: Fn(&IRNode) -> bool + Copy,
{
    let mut count = 0;
    for node in nodes {
        if pred(node) {
            count += 1;
        }
        match node {
            IRNode::Block { children } => {
                count += count_nodes_recursive(children, pred);
            }
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                count += count_nodes_recursive(std::slice::from_ref(then_branch.as_ref()), pred);
                count += count_nodes_recursive(std::slice::from_ref(else_branch.as_ref()), pred);
            }
            IRNode::Let { value, .. } => {
                count += count_nodes_recursive(std::slice::from_ref(value.as_ref()), pred);
            }
            _ => {}
        }
    }
    count
}

/// Generate requires/ensures/error_bound functions for all spec functions
pub fn generate_spec_functions(program: &mut Program) {
    // Collect spec function IDs (only base/runtime variants)
    let spec_func_ids: Vec<_> = program
        .functions
        .iter()
        .filter(|(id, f)| id.is_runtime() && f.is_spec())
        .map(|(id, _)| id)
        .collect();

    for func_id in spec_func_ids {
        // Collect counts upfront to avoid borrow issues with program
        let (requires_count, ensures_count, error_bound_count, error_bound_relative_count) = {
            let func = program.functions.get(&func_id);
            let body_slice = std::slice::from_ref(&func.body);
            (
                count_nodes_recursive(body_slice, |n| matches!(n, IRNode::Requires(_))),
                count_nodes_recursive(body_slice, |n| matches!(n, IRNode::Ensures(_))),
                count_nodes_recursive(body_slice, |n| matches!(n, IRNode::ErrorBound(_))),
                count_nodes_recursive(body_slice, |n| {
                    matches!(n, IRNode::ErrorBoundRelative { .. })
                }),
            )
        };

        // Generate .requires variant if any requires exist
        // Spec functions call other spec functions - no rewriting needed
        // Returns Prop (logical proposition)
        if requires_count > 0 {
            program.create_variant(func_id, FunctionVariant::Requires, Type::Prop, |body| {
                transform_spec_body(body, SpecExtract::Requires)
            });
        }

        // Generate .ensures variants for each ensures clause
        // Returns Prop (logical proposition)
        for idx in 0..ensures_count {
            program.create_variant(func_id, FunctionVariant::Ensures(idx), Type::Prop, |body| {
                transform_spec_body(body, SpecExtract::Ensures(idx))
            });
        }

        // Generate .error_bound variant if any error bounds exist
        // The error bound variant extracts the bound value from the ErrorBound node
        if error_bound_count > 0 {
            program.create_variant(
                func_id,
                FunctionVariant::ErrorBound,
                Type::UInt(64), // error bounds are u64
                |body| transform_spec_body(body, SpecExtract::ErrorBound),
            );
        }

        // Generate .error_bound_relative variant if any relative error bounds exist
        // Returns a tuple of (numerator, denominator) for the relative error fraction
        if error_bound_relative_count > 0 {
            program.create_variant(
                func_id,
                FunctionVariant::ErrorBoundRelative,
                Type::Tuple(vec![Type::UInt(64), Type::UInt(64)]), // (numerator, denominator)
                |body| transform_spec_body(body, SpecExtract::ErrorBoundRelative),
            );
        }
    }
}

/// What to extract from the spec function body
enum SpecExtract {
    Requires,
    Ensures(usize),
    ErrorBound,
    ErrorBoundRelative,
}

/// Transform spec function body to extract requires, ensures, or error bound conditions.
///
/// This extracts the boolean condition from Requires/Ensures nodes,
/// or the bound value from ErrorBound nodes,
/// keeping any necessary context (let bindings, control flow) that leads up to them.
fn transform_spec_body(node: &IRNode, extract: SpecExtract) -> IRNode {
    // For Requires: extract just the requires condition(s)
    // For Ensures: extract the specified ensures condition
    // For ErrorBound: extract the error bound value
    // For ErrorBoundRelative: extract (numerator, denominator) tuple
    match extract {
        SpecExtract::Requires => extract_requires(node),
        SpecExtract::Ensures(idx) => extract_ensures(node, idx),
        SpecExtract::ErrorBound => extract_error_bound(node),
        SpecExtract::ErrorBoundRelative => extract_error_bound_relative(node),
    }
}

/// Extract requires condition(s) from a spec body.
/// Keeps all leading let bindings and control flow, replaces Requires(cond) with cond.
fn extract_requires(node: &IRNode) -> IRNode {
    match node {
        IRNode::Block { children } => {
            // Find the index of the last Requires (or If containing Requires)
            let last_requires_idx = children.iter().rposition(contains_requires);

            match last_requires_idx {
                Some(idx) => {
                    // Keep everything up to and including the requires
                    let kept: Vec<IRNode> = children[..=idx]
                        .iter()
                        .map(extract_requires)
                        .collect();

                    // Filter out empty units
                    let kept: Vec<IRNode> = kept
                        .into_iter()
                        .filter(|n| !matches!(n, IRNode::Tuple(v) if v.is_empty()))
                        .collect();

                    if kept.is_empty() {
                        IRNode::Const(Const::Bool(true))
                    } else if kept.len() == 1 {
                        kept.into_iter().next().unwrap()
                    } else {
                        IRNode::Block { children: kept }
                    }
                }
                None => IRNode::Const(Const::Bool(true)),
            }
        }
        IRNode::Requires(cond) => *cond.clone(),
        IRNode::Ensures(_) => IRNode::unit(), // Filter out ensures in requires extraction
        IRNode::Return(_) => IRNode::unit(),  // Filter out returns
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // If both branches contain requires, transform both
            if contains_requires(then_branch) || contains_requires(else_branch) {
                IRNode::If {
                    cond: cond.clone(),
                    then_branch: Box::new(extract_requires(then_branch)),
                    else_branch: Box::new(extract_requires(else_branch)),
                }
            } else {
                IRNode::unit()
            }
        }
        IRNode::Let { pattern, value } => {
            // Keep let bindings as-is (they may define variables used in conditions)
            IRNode::Let {
                pattern: pattern.clone(),
                value: value.clone(),
            }
        }
        other => other.clone(),
    }
}

/// Check if a node contains any Requires node (directly or in children)
fn contains_requires(node: &IRNode) -> bool {
    match node {
        IRNode::Requires(_) => true,
        IRNode::Block { children } => children.iter().any(contains_requires),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => contains_requires(then_branch) || contains_requires(else_branch),
        IRNode::Let { value, .. } => contains_requires(value),
        _ => false,
    }
}

/// Extract the specified ensures condition from a spec body.
/// This collects let bindings that appear BEFORE the target ensures,
/// then extracts the ensures condition itself.
fn extract_ensures(node: &IRNode, target_idx: usize) -> IRNode {
    let mut counter = 0;
    let mut lets_before = Vec::new();
    let condition = extract_ensures_with_context(node, target_idx, &mut counter, &mut lets_before);

    // Build the result: Let bindings that precede the target ensures, followed by the condition
    if lets_before.is_empty() {
        condition
    } else {
        let mut children: Vec<IRNode> = lets_before
            .into_iter()
            .map(|(pattern, value)| IRNode::Let { pattern, value })
            .collect();
        children.push(condition);
        IRNode::Block { children }
    }
}

/// Extract ensures condition at target_idx, collecting let bindings that appear before it.
/// Returns the condition when found, and populates lets_before with preceding let bindings.
fn extract_ensures_with_context(
    node: &IRNode,
    target_idx: usize,
    counter: &mut usize,
    lets_before: &mut Vec<(Vec<String>, Box<IRNode>)>,
) -> IRNode {
    match node {
        IRNode::Block { children } => {
            for child in children {
                // First, check if this child is a Let binding that we might need to keep
                if let IRNode::Let { pattern, value } = child {
                    // Check if the target ensures is inside this Let's value
                    let ensures_in_value =
                        count_nodes_recursive(std::slice::from_ref(value.as_ref()), |n| {
                            matches!(n, IRNode::Ensures(_))
                        });

                    if ensures_in_value > 0 {
                        // The ensures is inside this Let - recurse into value
                        // Don't add this let to lets_before (it's part of the ensures)
                        let result =
                            extract_ensures_with_context(value, target_idx, counter, lets_before);
                        if !matches!(result, IRNode::Tuple(ref v) if v.is_empty()) {
                            return result;
                        }
                    } else {
                        // No ensures inside this Let - it's context we might need
                        // Only add it if we haven't found the target yet
                        lets_before.push((pattern.clone(), value.clone()));
                    }
                } else {
                    // Not a Let - check if target ensures is here
                    let result =
                        extract_ensures_with_context(child, target_idx, counter, lets_before);
                    if !matches!(result, IRNode::Tuple(ref v) if v.is_empty()) {
                        return result;
                    }
                }
            }
            IRNode::unit()
        }
        IRNode::Ensures(cond) => {
            let current = *counter;
            *counter += 1;
            if current == target_idx {
                *cond.clone()
            } else {
                IRNode::unit()
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Save current state of lets_before
            let lets_len = lets_before.len();

            // Check if target is in then_branch
            let then_result =
                extract_ensures_with_context(then_branch, target_idx, counter, lets_before);
            if !matches!(then_result, IRNode::Tuple(ref v) if v.is_empty()) {
                // Target was in then_branch - wrap in If
                return IRNode::If {
                    cond: cond.clone(),
                    then_branch: Box::new(then_result),
                    else_branch: Box::new(IRNode::Const(Const::Bool(true))),
                };
            }

            // Restore lets_before state before checking else_branch
            lets_before.truncate(lets_len);

            // Check if target is in else_branch
            let else_result =
                extract_ensures_with_context(else_branch, target_idx, counter, lets_before);
            if !matches!(else_result, IRNode::Tuple(ref v) if v.is_empty()) {
                // Target was in else_branch - wrap in If
                return IRNode::If {
                    cond: cond.clone(),
                    then_branch: Box::new(IRNode::Const(Const::Bool(true))),
                    else_branch: Box::new(else_result),
                };
            }
            IRNode::unit()
        }
        IRNode::Let { value, .. } => {
            // Recurse into Let values to find ensures inside
            // (matches count_nodes_recursive behavior)
            extract_ensures_with_context(value, target_idx, counter, lets_before)
        }
        _ => IRNode::unit(),
    }
}

/// Extract the error bound value from a spec body.
/// Returns a Block containing necessary Let bindings and the error bound value.
fn extract_error_bound(node: &IRNode) -> IRNode {
    // First, collect all Let bindings and find the ErrorBound value
    fn find_error_bound_value(node: &IRNode) -> Option<IRNode> {
        match node {
            IRNode::Block { children } => {
                for child in children {
                    if let Some(val) = find_error_bound_value(child) {
                        return Some(val);
                    }
                }
                None
            }
            IRNode::ErrorBound(bound) => Some(*bound.clone()),
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => {
                find_error_bound_value(then_branch).or_else(|| find_error_bound_value(else_branch))
            }
            IRNode::Let { value, .. } => find_error_bound_value(value),
            _ => None,
        }
    }

    fn collect_lets(node: &IRNode) -> Vec<(Vec<String>, Box<IRNode>)> {
        match node {
            IRNode::Block { children } => children.iter().flat_map(collect_lets).collect(),
            IRNode::Let { pattern, value } => {
                vec![(pattern.clone(), value.clone())]
            }
            _ => vec![],
        }
    }

    // Get the error bound value expression
    let error_value = find_error_bound_value(node).unwrap_or_else(|| {
        IRNode::Const(Const::UInt {
            bits: 64,
            value: 0u64.into(),
        })
    });

    // Collect all Let bindings from the body
    let lets = collect_lets(node);

    // Build the result: all Let bindings followed by the error value
    if lets.is_empty() {
        error_value
    } else {
        let mut children: Vec<IRNode> = lets
            .into_iter()
            .map(|(pattern, value)| IRNode::Let { pattern, value })
            .collect();
        children.push(error_value);
        IRNode::Block { children }
    }
}

/// Extract the relative error bound values from a spec body.
/// Returns a Tuple containing (numerator, denominator) for the relative error fraction.
fn extract_error_bound_relative(node: &IRNode) -> IRNode {
    // Find ErrorBoundRelative node and extract numerator and denominator
    fn find_error_bound_relative_values(node: &IRNode) -> Option<(IRNode, IRNode)> {
        match node {
            IRNode::Block { children } => {
                for child in children {
                    if let Some(val) = find_error_bound_relative_values(child) {
                        return Some(val);
                    }
                }
                None
            }
            IRNode::ErrorBoundRelative {
                numerator,
                denominator,
            } => Some((*numerator.clone(), *denominator.clone())),
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => find_error_bound_relative_values(then_branch)
                .or_else(|| find_error_bound_relative_values(else_branch)),
            IRNode::Let { value, .. } => find_error_bound_relative_values(value),
            _ => None,
        }
    }

    fn collect_lets(node: &IRNode) -> Vec<(Vec<String>, Box<IRNode>)> {
        match node {
            IRNode::Block { children } => children.iter().flat_map(collect_lets).collect(),
            IRNode::Let { pattern, value } => {
                vec![(pattern.clone(), value.clone())]
            }
            _ => vec![],
        }
    }

    // Get the relative error bound values
    let (numerator, denominator) = find_error_bound_relative_values(node).unwrap_or_else(|| {
        (
            IRNode::Const(Const::UInt {
                bits: 64,
                value: 0u64.into(),
            }),
            IRNode::Const(Const::UInt {
                bits: 64,
                value: 1u64.into(),
            }),
        )
    });

    // Build the tuple result
    let result = IRNode::Tuple(vec![numerator, denominator]);

    // Collect all Let bindings from the body
    let lets = collect_lets(node);

    // Build the result: all Let bindings followed by the tuple
    if lets.is_empty() {
        result
    } else {
        let mut children: Vec<IRNode> = lets
            .into_iter()
            .map(|(pattern, value)| IRNode::Let { pattern, value })
            .collect();
        children.push(result);
        IRNode::Block { children }
    }
}
