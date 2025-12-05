// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates requires/ensures IR functions from spec functions.
//!
//! For functions marked with #[spec(prove)], this pass:
//! 1. Extracts IRNode::Requires and IRNode::Ensures calls from the body
//! 2. Creates separate `.requires` and `.ensures` IR functions
//! 3. Adds them to the program for rendering

use crate::data::Program;
use crate::{IRNode, Function, FunctionSignature, Parameter, Type, BinOp, FunctionID};
use std::collections::BTreeMap;

/// Generate requires/ensures functions for all spec functions
pub fn generate_spec_functions(program: &mut Program) {
    let mut new_functions = Vec::new();

    // Build a map of runtime functions to their .pure variants
    // We look for functions ending in ".pure" and map back to the original
    let mut pure_map: BTreeMap<FunctionID, FunctionID> = BTreeMap::new();
    for (func_id, func) in &program.functions {
        if let Some(base_name) = func.name.strip_suffix(".pure") {
            // Find the original function with this base name
            for (orig_id, orig_func) in &program.functions {
                if orig_func.name == base_name {
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

        // Generate requires function - combines all requires() with &&
        if let Some(requires_fn) = generate_requires_function(func, &pure_map) {
            new_functions.push(requires_fn);
        }

        // Generate separate ensures functions - one per ensures() call
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
/// Copies the full function body but removes Ensures nodes and combines Requires with &&
fn generate_requires_function(spec_func: &Function, pure_map: &BTreeMap<FunctionID, FunctionID>) -> Option<Function> {
    // Collect all requires expressions from the body
    let mut requires_exprs = Vec::new();
    for node in spec_func.body.iter() {
        if let IRNode::Requires(cond) = node {
            requires_exprs.push((**cond).clone());
        }
    }

    if requires_exprs.is_empty() {
        return None;
    }

    // Copy the full body and remove Requires/Ensures nodes
    let body = remove_spec_nodes(&spec_func.body);

    // Combine all requires with && and use that as the return value
    let combined_requires = if requires_exprs.len() == 1 {
        requires_exprs.into_iter().next().unwrap()
    } else {
        requires_exprs.into_iter().reduce(|acc, req| {
            IRNode::BinOp {
                op: BinOp::And,
                lhs: Box::new(acc),
                rhs: Box::new(req),
            }
        }).unwrap()
    };

    // Replace the final return with the combined requires
    let body = replace_final_return(body, combined_requires);

    // Transform function calls to use .pure variants
    let body = transform_to_pure_calls(body, pure_map);

    Some(Function {
        module_id: spec_func.module_id,
        name: format!("{}.requires", spec_func.name),
        signature: FunctionSignature {
            type_params: spec_func.signature.type_params.clone(),
            parameters: spec_func.signature.parameters.clone(),
            return_type: Type::Prop,
        },
        body,
        variables: spec_func.variables.clone(),
        mutual_group_id: None,
        is_native: false,
        is_spec_function: false,
    })
}

/// Generate .ensures functions from a spec function
/// Creates one separate function per ensures() call
fn generate_ensures_functions(spec_func: &Function, pure_map: &BTreeMap<FunctionID, FunctionID>) -> Vec<Function> {
    // Collect all ensures expressions from the body
    let mut ensures_exprs = Vec::new();
    for node in spec_func.body.iter() {
        if let IRNode::Ensures(cond) = node {
            ensures_exprs.push((**cond).clone());
        }
    }

    if ensures_exprs.is_empty() {
        return vec![];
    }

    // The ensures function needs the parameters + result parameter
    let mut parameters = spec_func.signature.parameters.clone();

    // Add result parameter - extract return type from spec function
    let result_type = spec_func.signature.return_type
        .unwrap_monad()
        .cloned()
        .unwrap_or_else(|| spec_func.signature.return_type.clone());

    parameters.push(Parameter {
        name: "result".to_string(),
        param_type: result_type,
        ssa_value: "$result".to_string(),
    });

    // Generate one function per ensures expression
    ensures_exprs.into_iter().enumerate().map(|(i, ensures_expr)| {
        // Copy the full body and remove Requires/Ensures nodes
        let body = remove_spec_nodes(&spec_func.body);

        // Replace the final return with this ensures expression
        let body = replace_final_return(body, ensures_expr);

        // Transform function calls to use .pure variants
        let body = transform_to_pure_calls(body, pure_map);

        let name = if i == 0 {
            format!("{}.ensures", spec_func.name)
        } else {
            format!("{}.ensures_{}", spec_func.name, i + 1)
        };

        Function {
            module_id: spec_func.module_id,
            name,
            signature: FunctionSignature {
                type_params: spec_func.signature.type_params.clone(),
                parameters: parameters.clone(),
                return_type: Type::Prop,
            },
            body,
            variables: spec_func.variables.clone(),
            mutual_group_id: None,
            is_native: false,
            is_spec_function: false,
        }
    }).collect()
}

/// Remove Requires and Ensures nodes from IR tree
fn remove_spec_nodes(node: &IRNode) -> IRNode {
    node.clone().map(&mut |n| match n {
        IRNode::Block { children } => {
            let filtered: Vec<_> = children.into_iter()
                .filter(|c| !matches!(c, IRNode::Requires(_) | IRNode::Ensures(_)))
                .collect();
            IRNode::Block { children: filtered }
        }
        other => other,
    })
}

/// Replace the final return value in the IR tree with a new expression
fn replace_final_return(node: IRNode, new_return: IRNode) -> IRNode {
    match node {
        IRNode::Block { mut children } => {
            if let Some(last) = children.last_mut() {
                *last = replace_final_return(last.clone(), new_return);
            }
            IRNode::Block { children }
        }
        // If the node itself is the final expression, replace it
        _ => new_return,
    }
}

/// Transform function calls to use .pure variants with proof arguments
fn transform_to_pure_calls(node: IRNode, pure_map: &BTreeMap<FunctionID, FunctionID>) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Call { function, type_args, mut args } => {
            // Replace with .pure variant if it exists
            if let Some(&pure_id) = pure_map.get(&function) {
                // Add proof argument for .pure calls
                args.push(IRNode::Var("$proof".to_string()));
                IRNode::Call {
                    function: pure_id,
                    type_args,
                    args,
                }
            } else {
                IRNode::Call {
                    function,
                    type_args,
                    args,
                }
            }
        }
        other => other,
    })
}
