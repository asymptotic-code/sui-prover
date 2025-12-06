// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates requires/ensures IR functions from spec functions.
//!
//! For functions marked with #[spec(prove)], this pass:
//! 1. Copies the function body
//! 2. Extracts IRNode::Requires and IRNode::Ensures calls
//! 3. Replaces the return with AND of all requires/ensures conditions
//! 4. Creates separate `.requires` and `.ensures` IR functions

use crate::data::Program;
use crate::{IRNode, Function, FunctionSignature, Type, BinOp, FunctionID, Const};
use std::collections::BTreeMap;

/// Generate requires/ensures functions for all spec functions
pub fn generate_spec_functions(program: &mut Program) {
    let mut new_functions = Vec::new();

    // Build a map of runtime functions to their .pure variants
    // We look for functions ending in ".pure" and map back to the original
    // IMPORTANT: Also match on module_id to avoid cross-module mismatches (e.g., I32.from vs I128.from)
    let mut pure_map: BTreeMap<FunctionID, FunctionID> = BTreeMap::new();
    for (func_id, func) in &program.functions {
        if let Some(base_name) = func.name.strip_suffix(".pure") {
            // Find the original function with this base name IN THE SAME MODULE
            for (orig_id, orig_func) in &program.functions {
                if orig_func.name == base_name && orig_func.module_id == func.module_id {
                    pure_map.insert(*orig_id, *func_id);
                    break;
                }
            }
        }
    }

    for (_func_id, func) in &program.functions {
        if !func.is_spec_function {
            continue;
        }

        // Generate requires function - copies body, replaces return with AND of requires conditions
        if let Some(requires_fn) = generate_requires_function(func, &pure_map) {
            new_functions.push(requires_fn);
        }

        // Generate ensures function - copies body, replaces return with AND of ensures conditions
        new_functions.extend(generate_ensures_functions(func, &pure_map));
    }

    // Add new functions to the program
    let next_id = program.functions.len();
    for (i, func) in new_functions.into_iter().enumerate() {
        let id = next_id + i;
        program.functions.items.insert(id, func);
    }
}

/// Generate a .requires function from a spec function
fn generate_requires_function(
    spec_func: &Function,
    pure_map: &BTreeMap<FunctionID, FunctionID>,
) -> Option<Function> {
    // Check if there are any requires
    let has_requires = spec_func.body.iter().any(|n| matches!(n, IRNode::Requires(_)));
    if !has_requires {
        return None;
    }

    // Transform body: capture Requires conditions, remove Ensures, replace Return
    let body = transform_body_for_requires(spec_func.body.clone());

    // Transform function calls to use .pure variants
    let body = transform_to_pure_calls(body, pure_map);

    Some(Function {
        module_id: spec_func.module_id,
        name: format!("{}.requires", spec_func.name),
        signature: FunctionSignature {
            type_params: spec_func.signature.type_params.clone(),
            parameters: spec_func.signature.parameters.clone(),
            return_type: Type::Bool,
        },
        body,
        variables: spec_func.variables.clone(),
        mutual_group_id: None,
        is_native: false,
        is_spec_function: false,
        is_monadic: false,  // .requires returns Bool, not Except
    })
}

/// Generate .ensures functions from a spec function
/// Creates one function per ensures() call, each returning that specific condition
fn generate_ensures_functions(
    spec_func: &Function,
    pure_map: &BTreeMap<FunctionID, FunctionID>,
) -> Vec<Function> {
    // Count ensures to generate separate functions
    let ensures_count = spec_func.body.iter().filter(|n| matches!(n, IRNode::Ensures(_))).count();
    if ensures_count == 0 {
        return vec![];
    }

    // Generate one function per ensures
    (0..ensures_count)
        .map(|idx| {
            let body = transform_body_for_ensures_n(spec_func.body.clone(), idx);
            let body = transform_to_pure_calls(body, pure_map);

            let name = if ensures_count == 1 {
                format!("{}.ensures", spec_func.name)
            } else {
                format!("{}.ensures_{}", spec_func.name, idx)
            };

            Function {
                module_id: spec_func.module_id,
                name,
                signature: FunctionSignature {
                    type_params: spec_func.signature.type_params.clone(),
                    parameters: spec_func.signature.parameters.clone(),
                    return_type: Type::Bool,
                },
                body,
                variables: spec_func.variables.clone(),
                mutual_group_id: None,
                is_native: false,
                is_spec_function: false,
                is_monadic: false,  // .ensures returns Bool, not Except
            }
        })
        .collect()
}

/// Combine expressions with AND
fn combine_with_and(exprs: Vec<IRNode>) -> IRNode {
    exprs.into_iter().reduce(|acc, expr| {
        IRNode::BinOp {
            op: BinOp::And,
            lhs: Box::new(acc),
            rhs: Box::new(expr),
        }
    }).unwrap_or(IRNode::Const(Const::Bool(true)))
}

/// Transform body for .requires function:
/// Walk through the IR, replacing Requires with let bindings, removing Ensures/Return,
/// and appending the combined condition at the end.
fn transform_body_for_requires(node: IRNode) -> IRNode {
    let mut counter = 0;
    let mut captured_vars = Vec::new();

    // Transform the tree: replace Requires with let bindings
    let transformed = node.map(&mut |n| match n {
        IRNode::Requires(cond) => {
            let var_name = format!("$requires_{}", counter);
            counter += 1;
            captured_vars.push(var_name.clone());
            IRNode::Let {
                pattern: vec![var_name],
                value: cond,
            }
        }
        other => other,
    });

    // Filter out Ensures and Return nodes
    let transformed = transformed.filter(|n| {
        !matches!(n, IRNode::Ensures(_) | IRNode::Return(_))
    });

    if captured_vars.is_empty() {
        return IRNode::Const(Const::Bool(true));
    }

    // Append the combined condition
    let combined = combine_with_and(
        captured_vars.into_iter().map(IRNode::Var).collect()
    );

    transformed.combine(combined)
}

/// Transform body for the Nth ensures function:
/// Keep all code, but remove Requires, keep only the Nth Ensures as the result,
/// and remove Return nodes.
fn transform_body_for_ensures_n(node: IRNode, target_idx: usize) -> IRNode {
    let mut counter = 0;
    let mut target_cond = None;

    // Transform the tree: capture Nth Ensures condition
    let transformed = node.map(&mut |n| match n {
        IRNode::Ensures(ref cond) => {
            if counter == target_idx {
                target_cond = Some((**cond).clone());
            }
            counter += 1;
            n  // Keep the Ensures node for now, we'll filter it out
        }
        other => other,
    });

    // Filter out Requires, Ensures, and Return nodes
    let transformed = transformed.filter(|n| {
        !matches!(n, IRNode::Requires(_) | IRNode::Ensures(_) | IRNode::Return(_))
    });

    // Append the target condition
    match target_cond {
        Some(cond) => transformed.combine(cond),
        None => IRNode::Const(Const::Bool(true)),
    }
}

/// Transform function calls to use .pure variants (same args as the original function)
fn transform_to_pure_calls(node: IRNode, pure_map: &BTreeMap<FunctionID, FunctionID>) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Call { function, type_args, args } => {
            if let Some(&pure_id) = pure_map.get(&function) {
                IRNode::Call {
                    function: pure_id,
                    type_args,
                    args,
                }
            } else {
                IRNode::Call { function, type_args, args }
            }
        }
        other => other,
    })
}
