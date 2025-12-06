// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates .aborts and .pure variants for all runtime functions
//!
//! For each non-spec, non-native function, this pass generates:
//! - `.aborts` : Prop - predicate indicating when the function aborts
//! - `.pure` : non-monadic version that calls other .pure functions

use crate::data::Program;
use crate::{IRNode, Function, FunctionSignature, Type, Const, FunctionID};
use std::collections::BTreeMap;

/// Generate .aborts and .pure variants for all runtime functions.
///
/// Prerequisites: `analyze_monadicity` must have run first to set `is_monadic` on functions.
pub fn generate_runtime_variants(program: &mut Program) {
    let mut aborts_map = BTreeMap::new(); // original_id -> aborts_id
    let mut pure_map = BTreeMap::new();   // original_id -> pure_id
    let mut new_functions = Vec::new();   // (id, function) pairs to insert

    // Collect IDs and functions in order
    let original_funcs: Vec<_> = program.functions.iter_ids()
        .map(|id| (id, program.functions.get(id).clone()))
        .collect();

    let next_id = program.functions.len();
    let mut current_id = next_id;

    // Generate variants in the same order as original functions
    // For each original function, generate .aborts then .pure immediately after
    for (func_id, func) in &original_funcs {
        // Skip spec functions, native functions, and non-monadic functions
        // is_monadic is set by analyze_monadicity pass
        if func.is_spec_function || func.is_native || !func.is_monadic {
            continue;
        }

        // Generate .aborts function
        let aborts_fn = generate_aborts_function(func);
        let aborts_id = current_id;
        aborts_map.insert(*func_id, aborts_id);
        new_functions.push((aborts_id, aborts_fn));
        current_id += 1;

        // Generate .pure function
        let pure_fn = generate_pure_function(func);
        let pure_id = current_id;
        pure_map.insert(*func_id, pure_id);
        new_functions.push((pure_id, pure_fn));
        current_id += 1;
    }

    // Add all new functions to the program
    for (id, func) in new_functions {
        program.functions.items.insert(id, func);
    }

    // Second pass: rewrite function IDs in .aborts and .pure bodies
    rewrite_variant_calls(program, &aborts_map, &pure_map);
}

/// Generate a .aborts function that returns Bool (rendered as Prop) indicating when function aborts
fn generate_aborts_function(func: &Function) -> Function {
    // Copy the full body and convert to abort predicate
    let body = convert_to_aborts_predicate(&func.body);

    Function {
        module_id: func.module_id,
        name: format!("{}.aborts", func.name),
        signature: FunctionSignature {
            type_params: func.signature.type_params.clone(),
            parameters: func.signature.parameters.clone(),
            return_type: Type::Bool,
        },
        body,
        variables: func.variables.clone(),
        mutual_group_id: None,
        is_native: false,
        is_spec_function: false,
        is_monadic: false,  // .aborts returns Bool, not Except
    }
}

/// Generate a .pure function that is non-monadic
/// Pure functions have the same parameters as the original function.
fn generate_pure_function(func: &Function) -> Function {
    // Unwrap return type from Except monad
    let return_type = func.signature.return_type
        .unwrap_monad()
        .cloned()
        .unwrap_or_else(|| func.signature.return_type.clone());

    // Copy the full body and convert to pure (non-monadic)
    let body = convert_to_pure(&func.body);

    Function {
        module_id: func.module_id,
        name: format!("{}.pure", func.name),
        signature: FunctionSignature {
            type_params: func.signature.type_params.clone(),
            parameters: func.signature.parameters.clone(),
            return_type,
        },
        body,
        variables: func.variables.clone(),
        mutual_group_id: None,
        is_native: false,
        is_spec_function: false,
        is_monadic: false,  // .pure is non-monadic by definition
    }
}

/// Convert monadic IR to abort predicate (returns Prop)
/// Abort becomes True, Return becomes False, everything else recurses.
fn convert_to_aborts_predicate(node: &IRNode) -> IRNode {
    node.clone().map(&mut |n| match n {
        IRNode::Abort(_) => IRNode::Const(Const::Bool(true)),
        IRNode::Return(_) => IRNode::Const(Const::Bool(false)),
        // Spec nodes shouldn't appear in runtime functions, unwrap them
        IRNode::Requires(inner) | IRNode::Ensures(inner) => *inner,
        other => other,
    })
}

/// Convert monadic IR to pure (non-monadic) version
/// Uses a two-pass approach: first simplify If nodes with aborting branches,
/// then filter out Abort nodes and unwrap Returns.
fn convert_to_pure(node: &IRNode) -> IRNode {
    // First pass: simplify If nodes where one or both branches always abort
    let node = simplify_aborting_ifs(node.clone());

    // Second pass: filter out Abort nodes from blocks, unwrap Returns
    node.filter(|n| !matches!(n, IRNode::Abort(_)))
        .map(&mut |n| match n {
            IRNode::Return(vals) => {
                if vals.len() == 1 {
                    vals.into_iter().next().unwrap()
                } else {
                    IRNode::Tuple(vals)
                }
            }
            // Spec nodes shouldn't appear in runtime functions, unwrap them
            IRNode::Requires(inner) | IRNode::Ensures(inner) => *inner,
            other => other,
        })
}

/// Simplify If nodes where branches always abort
fn simplify_aborting_ifs(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If { cond, then_branch, else_branch } => {
            let then_always_aborts = then_branch.always_aborts();
            let else_always_aborts = else_branch.always_aborts();

            if then_always_aborts && else_always_aborts {
                IRNode::unit()
            } else if then_always_aborts {
                *else_branch
            } else if else_always_aborts {
                *then_branch
            } else {
                IRNode::If { cond, then_branch, else_branch }
            }
        }
        other => other,
    })
}

/// Rewrite function calls in .aborts and .pure variants to call their respective variants
fn rewrite_variant_calls(
    program: &mut Program,
    aborts_map: &BTreeMap<FunctionID, FunctionID>,
    pure_map: &BTreeMap<FunctionID, FunctionID>,
) {
    // Rewrite calls in .aborts functions
    for &aborts_id in aborts_map.values() {
        let func = program.functions.get_mut(aborts_id);
        func.body = rewrite_calls_to_aborts(&func.body, pure_map);
    }

    // Rewrite calls in .pure functions
    for &pure_id in pure_map.values() {
        let func = program.functions.get_mut(pure_id);
        func.body = rewrite_calls_to_pure(&func.body, pure_map);
    }
}

/// Rewrite function calls in .aborts functions to use .pure variants
fn rewrite_calls_to_aborts(
    node: &IRNode,
    pure_map: &BTreeMap<FunctionID, FunctionID>,
) -> IRNode {
    node.clone().map(&mut |n| match n {
        IRNode::Call { function, type_args, args } => {
            let new_function = *pure_map.get(&function).unwrap_or(&function);
            IRNode::Call {
                function: new_function,
                type_args,
                args,
            }
        }
        other => other,
    })
}

/// Rewrite function calls to use .pure variants (same args as original)
fn rewrite_calls_to_pure(node: &IRNode, pure_map: &BTreeMap<FunctionID, FunctionID>) -> IRNode {
    node.clone().map(&mut |n| match n {
        IRNode::Call { function, type_args, args } => {
            // Replace with .pure variant if it exists (same args)
            let new_function = *pure_map.get(&function).unwrap_or(&function);
            IRNode::Call {
                function: new_function,
                type_args,
                args,
            }
        }
        other => other,
    })
}
