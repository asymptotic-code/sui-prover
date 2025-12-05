// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates .aborts and .pure variants for all runtime functions
//!
//! For each non-spec, non-native function, this pass generates:
//! - `.aborts` : Prop - predicate indicating when the function aborts
//! - `.pure` : non-monadic version that calls other .pure functions

use crate::data::Program;
use crate::{IRNode, Function, FunctionSignature, Parameter, Type, Const, FunctionID};
use std::collections::{BTreeMap, BTreeSet};

/// Generate .aborts and .pure variants for all runtime functions
pub fn generate_runtime_variants(program: &mut Program) {
    let mut aborts_map = BTreeMap::new(); // original_id -> aborts_id
    let mut pure_map = BTreeMap::new();   // original_id -> pure_id
    let mut new_functions = Vec::new();   // (id, function) pairs to insert

    // Collect IDs and functions in order
    let original_funcs: Vec<_> = program.functions.iter_ids()
        .map(|id| (id, program.functions.get(id).clone()))
        .collect();

    // Determine which functions are truly monadic (like monadicity analysis does)
    // This is necessary because all functions start with Except-wrapped return types,
    // but monadicity analysis hasn't run yet to unwrap the non-monadic ones
    let monadic_funcs = compute_monadic_functions(&original_funcs);

    let next_id = program.functions.len();
    let mut current_id = next_id;

    // Generate variants in the same order as original functions
    // For each original function, generate .aborts then .pure immediately after
    for (func_id, func) in &original_funcs {
        // Skip spec functions, native functions, and non-monadic functions
        if func.is_spec_function || func.is_native || !monadic_funcs.contains(func_id) {
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

/// Compute which functions are monadic (same logic as monadicity analysis)
fn compute_monadic_functions(funcs: &[(FunctionID, Function)]) -> BTreeSet<FunctionID> {
    let mut monadic_funcs = BTreeSet::new();

    // First pass: identify intrinsically monadic functions
    for (func_id, func) in funcs {
        if func.body.aborts() || func.is_native {
            monadic_funcs.insert(*func_id);
        }
    }

    // Iterate to fixed point to propagate monadicity
    loop {
        let mut changed = false;
        for (func_id, func) in funcs {
            if monadic_funcs.contains(func_id) {
                continue;
            }
            let calls_monadic = func.body.calls().any(|id| monadic_funcs.contains(&id));
            if calls_monadic {
                monadic_funcs.insert(*func_id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    monadic_funcs
}

/// Generate a .aborts function that returns Prop indicating when function aborts
fn generate_aborts_function(func: &Function) -> Function {
    // Copy the full body and convert to abort predicate
    let body = convert_to_aborts_predicate(&func.body);

    Function {
        module_id: func.module_id,
        name: format!("{}.aborts", func.name),
        signature: FunctionSignature {
            type_params: func.signature.type_params.clone(),
            parameters: func.signature.parameters.clone(),
            return_type: Type::Prop,
        },
        body,
        variables: func.variables.clone(),
        mutual_group_id: None,
        is_native: false,
        is_spec_function: false,
    }
}

/// Generate a .pure function that is non-monadic
fn generate_pure_function(func: &Function) -> Function {
    // Add ¬aborts proof parameter
    let mut parameters = func.signature.parameters.clone();
    parameters.push(Parameter {
        name: "h".to_string(),
        param_type: Type::Prop, // Actually ¬aborts, but we use Prop for now
        ssa_value: "$h".to_string(),
    });

    // Unwrap return type from Except monad
    let return_type = func.signature.return_type
        .unwrap_monad()
        .cloned()
        .unwrap_or_else(|| func.signature.return_type.clone());

    // Copy the full body and convert to pure (non-monadic)
    let body = convert_to_pure(&func.body, &func.name);

    Function {
        module_id: func.module_id,
        name: format!("{}.pure", func.name),
        signature: FunctionSignature {
            type_params: func.signature.type_params.clone(),
            parameters,
            return_type,
        },
        body,
        variables: func.variables.clone(),
        mutual_group_id: None,
        is_native: false,
        is_spec_function: false,
    }
}

/// Convert monadic IR to abort predicate (returns Prop)
/// This is complex because we need to track whether any called function aborts.
/// Strategy: replace let x ← f(...) with:
///   let x := f.pure(...)
///   if f.aborts(...) then true else <rest>
/// But for now, we'll use a simpler approach: just call .aborts variant directly
fn convert_to_aborts_predicate(node: &IRNode) -> IRNode {
    match node {
        // Abort becomes True
        IRNode::Abort(_) => IRNode::Const(Const::Bool(true)),

        // Return becomes False (doesn't abort)
        IRNode::Return(_) => IRNode::Const(Const::Bool(false)),

        // Let bindings: check if the value aborts OR the continuation aborts
        // This is handled by the IR rewriter which will insert .aborts calls
        IRNode::Let { pattern, value } => {
            IRNode::Let {
                pattern: pattern.clone(),
                value: Box::new(convert_to_aborts_predicate(value)),
            }
        }

        // Function calls will be rewritten to .aborts variants by rewrite_calls_to_aborts
        IRNode::Call { function, type_args, args } => {
            IRNode::Call {
                function: *function,
                type_args: type_args.clone(),
                args: args.iter().map(|a| convert_to_aborts_predicate(a)).collect(),
            }
        }

        // If branches are converted recursively
        IRNode::If { cond, then_branch, else_branch } => {
            IRNode::If {
                cond: Box::new(convert_to_aborts_predicate(cond)),
                then_branch: Box::new(convert_to_aborts_predicate(then_branch)),
                else_branch: Box::new(convert_to_aborts_predicate(else_branch)),
            }
        }

        // Block children are converted recursively
        IRNode::Block { children } => {
            IRNode::Block {
                children: children.iter().map(|c| convert_to_aborts_predicate(c)).collect(),
            }
        }

        // BinOp, UnOp, etc. recurse on their children
        IRNode::BinOp { op, lhs, rhs } => {
            IRNode::BinOp {
                op: *op,
                lhs: Box::new(convert_to_aborts_predicate(lhs)),
                rhs: Box::new(convert_to_aborts_predicate(rhs)),
            }
        }

        IRNode::UnOp { op, operand } => {
            IRNode::UnOp {
                op: *op,
                operand: Box::new(convert_to_aborts_predicate(operand)),
            }
        }

        // Leaf nodes stay the same
        IRNode::Var(_) | IRNode::Const(_) => node.clone(),

        // Pack, Field, Unpack, etc. recurse
        IRNode::Pack { struct_id, type_args, fields } => {
            IRNode::Pack {
                struct_id: *struct_id,
                type_args: type_args.clone(),
                fields: fields.iter().map(|f| convert_to_aborts_predicate(f)).collect(),
            }
        }

        IRNode::Field { base, struct_id, field_index } => {
            IRNode::Field {
                base: Box::new(convert_to_aborts_predicate(base)),
                struct_id: *struct_id,
                field_index: *field_index,
            }
        }

        IRNode::Unpack { struct_id, value } => {
            IRNode::Unpack {
                struct_id: *struct_id,
                value: Box::new(convert_to_aborts_predicate(value)),
            }
        }

        IRNode::Tuple(elems) => {
            IRNode::Tuple(elems.iter().map(|e| convert_to_aborts_predicate(e)).collect())
        }

        IRNode::VecOp { op, args } => {
            IRNode::VecOp {
                op: *op,
                args: args.iter().map(|a| convert_to_aborts_predicate(a)).collect(),
            }
        }

        IRNode::While { cond, body, vars } => {
            IRNode::While {
                cond: Box::new(convert_to_aborts_predicate(cond)),
                body: Box::new(convert_to_aborts_predicate(body)),
                vars: vars.clone(),
            }
        }

        IRNode::UpdateField { base, struct_id, field_index, value } => {
            IRNode::UpdateField {
                base: Box::new(convert_to_aborts_predicate(base)),
                struct_id: *struct_id,
                field_index: *field_index,
                value: Box::new(convert_to_aborts_predicate(value)),
            }
        }

        IRNode::UpdateVec { base, index, value } => {
            IRNode::UpdateVec {
                base: Box::new(convert_to_aborts_predicate(base)),
                index: Box::new(convert_to_aborts_predicate(index)),
                value: Box::new(convert_to_aborts_predicate(value)),
            }
        }

        // Spec nodes shouldn't appear in runtime functions, but handle them anyway
        IRNode::Requires(inner) | IRNode::Ensures(inner) => {
            convert_to_aborts_predicate(inner)
        }
    }
}

/// Convert monadic IR to pure (non-monadic) version
fn convert_to_pure(node: &IRNode, _func_name: &str) -> IRNode {
    match node {
        // Abort is unreachable in pure version (we have proof ¬aborts)
        // Backend will render this as absurd with the proof
        IRNode::Abort(_) => IRNode::unit(),

        // Return shouldn't appear in pure version either
        IRNode::Return(vals) => {
            if vals.len() == 1 {
                convert_to_pure(&vals[0], _func_name)
            } else {
                IRNode::Tuple(vals.iter().map(|v| convert_to_pure(v, _func_name)).collect())
            }
        }

        // Let bindings stay the same - no change needed, backend renders without ←
        IRNode::Let { pattern, value } => {
            IRNode::Let {
                pattern: pattern.clone(),
                value: Box::new(convert_to_pure(value, _func_name)),
            }
        }

        // Function calls stay the same - backend will add proof argument
        IRNode::Call { function, type_args, args } => {
            IRNode::Call {
                function: *function,
                type_args: type_args.clone(),
                args: args.iter().map(|a| convert_to_pure(a, _func_name)).collect(),
            }
        }

        // If branches converted recursively
        IRNode::If { cond, then_branch, else_branch } => {
            IRNode::If {
                cond: Box::new(convert_to_pure(cond, _func_name)),
                then_branch: Box::new(convert_to_pure(then_branch, _func_name)),
                else_branch: Box::new(convert_to_pure(else_branch, _func_name)),
            }
        }

        // Block children converted recursively
        IRNode::Block { children } => {
            IRNode::Block {
                children: children.iter().map(|c| convert_to_pure(c, _func_name)).collect(),
            }
        }

        // BinOp, UnOp, etc. recurse on their children
        IRNode::BinOp { op, lhs, rhs } => {
            IRNode::BinOp {
                op: *op,
                lhs: Box::new(convert_to_pure(lhs, _func_name)),
                rhs: Box::new(convert_to_pure(rhs, _func_name)),
            }
        }

        IRNode::UnOp { op, operand } => {
            IRNode::UnOp {
                op: *op,
                operand: Box::new(convert_to_pure(operand, _func_name)),
            }
        }

        // Leaf nodes stay the same
        IRNode::Var(_) | IRNode::Const(_) => node.clone(),

        // Pack, Field, Unpack, etc. recurse
        IRNode::Pack { struct_id, type_args, fields } => {
            IRNode::Pack {
                struct_id: *struct_id,
                type_args: type_args.clone(),
                fields: fields.iter().map(|f| convert_to_pure(f, _func_name)).collect(),
            }
        }

        IRNode::Field { base, struct_id, field_index } => {
            IRNode::Field {
                base: Box::new(convert_to_pure(base, _func_name)),
                struct_id: *struct_id,
                field_index: *field_index,
            }
        }

        IRNode::Unpack { struct_id, value } => {
            IRNode::Unpack {
                struct_id: *struct_id,
                value: Box::new(convert_to_pure(value, _func_name)),
            }
        }

        IRNode::Tuple(elems) => {
            IRNode::Tuple(elems.iter().map(|e| convert_to_pure(e, _func_name)).collect())
        }

        IRNode::VecOp { op, args } => {
            IRNode::VecOp {
                op: *op,
                args: args.iter().map(|a| convert_to_pure(a, _func_name)).collect(),
            }
        }

        IRNode::While { cond, body, vars } => {
            IRNode::While {
                cond: Box::new(convert_to_pure(cond, _func_name)),
                body: Box::new(convert_to_pure(body, _func_name)),
                vars: vars.clone(),
            }
        }

        IRNode::UpdateField { base, struct_id, field_index, value } => {
            IRNode::UpdateField {
                base: Box::new(convert_to_pure(base, _func_name)),
                struct_id: *struct_id,
                field_index: *field_index,
                value: Box::new(convert_to_pure(value, _func_name)),
            }
        }

        IRNode::UpdateVec { base, index, value } => {
            IRNode::UpdateVec {
                base: Box::new(convert_to_pure(base, _func_name)),
                index: Box::new(convert_to_pure(index, _func_name)),
                value: Box::new(convert_to_pure(value, _func_name)),
            }
        }

        // Spec nodes shouldn't appear in runtime functions
        IRNode::Requires(inner) | IRNode::Ensures(inner) => {
            convert_to_pure(inner, _func_name)
        }
    }
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
        func.body = rewrite_calls_to_aborts(&func.body, aborts_map, pure_map);
    }

    // Rewrite calls in .pure functions
    for &pure_id in pure_map.values() {
        let func = program.functions.get_mut(pure_id);
        func.body = rewrite_calls_to_pure(&func.body, pure_map);
    }
}

/// Rewrite function calls in .aborts functions to handle transitive aborts
/// For calls to monadic functions, we need to:
/// 1. Check if the called function aborts (using .aborts predicate)
/// 2. Use the .pure variant for the actual computation
/// This is done by transforming let-bindings appropriately
fn rewrite_calls_to_aborts(
    node: &IRNode,
    aborts_map: &BTreeMap<FunctionID, FunctionID>,
    pure_map: &BTreeMap<FunctionID, FunctionID>,
) -> IRNode {
    rewrite_calls_to_aborts_inner(node, aborts_map, pure_map)
}

fn rewrite_calls_to_aborts_inner(
    node: &IRNode,
    aborts_map: &BTreeMap<FunctionID, FunctionID>,
    pure_map: &BTreeMap<FunctionID, FunctionID>,
) -> IRNode {
    match node {
        // Atomic nodes - no recursion needed
        IRNode::Var(_) | IRNode::Const(_) => node.clone(),

        // Let bindings with monadic function calls need special handling
        IRNode::Let { pattern, value } => {
            // Check if value is a call to a function that has an aborts variant
            if let IRNode::Call { function, type_args, args } = &**value {
                if pure_map.contains_key(function) {
                    // This is a call to a monadic function
                    // Replace the call with .pure variant
                    let pure_id = pure_map[function];

                    // Call to .pure variant with proof placeholder
                    let mut pure_args: Vec<_> = args.iter()
                        .map(|a| rewrite_calls_to_aborts_inner(a, aborts_map, pure_map))
                        .collect();
                    pure_args.push(IRNode::Var("$proof".to_string()));

                    let pure_call = IRNode::Call {
                        function: pure_id,
                        type_args: type_args.clone(),
                        args: pure_args,
                    };

                    // Reconstruct let binding with pure call
                    return IRNode::Let {
                        pattern: pattern.clone(),
                        value: Box::new(pure_call),
                    };
                }
            }

            // Not a monadic call, recurse normally
            IRNode::Let {
                pattern: pattern.clone(),
                value: Box::new(rewrite_calls_to_aborts_inner(value, aborts_map, pure_map)),
            }
        }

        // For Call nodes, replace with .pure variant if available
        IRNode::Call { function, type_args, args } => {
            if pure_map.contains_key(function) {
                let pure_id = pure_map[function];
                let mut new_args: Vec<_> = args.iter()
                    .map(|a| rewrite_calls_to_aborts_inner(a, aborts_map, pure_map))
                    .collect();
                new_args.push(IRNode::Var("$proof".to_string()));
                IRNode::Call {
                    function: pure_id,
                    type_args: type_args.clone(),
                    args: new_args,
                }
            } else {
                IRNode::Call {
                    function: *function,
                    type_args: type_args.clone(),
                    args: args.iter().map(|a| rewrite_calls_to_aborts_inner(a, aborts_map, pure_map)).collect(),
                }
            }
        }

        // Block nodes
        IRNode::Block { children } => {
            IRNode::Block {
                children: children.iter().map(|c| rewrite_calls_to_aborts_inner(c, aborts_map, pure_map)).collect(),
            }
        }

        // If nodes
        IRNode::If { cond, then_branch, else_branch } => {
            IRNode::If {
                cond: Box::new(rewrite_calls_to_aborts_inner(cond, aborts_map, pure_map)),
                then_branch: Box::new(rewrite_calls_to_aborts_inner(then_branch, aborts_map, pure_map)),
                else_branch: Box::new(rewrite_calls_to_aborts_inner(else_branch, aborts_map, pure_map)),
            }
        }

        // BinOp nodes
        IRNode::BinOp { op, lhs, rhs } => {
            IRNode::BinOp {
                op: *op,
                lhs: Box::new(rewrite_calls_to_aborts_inner(lhs, aborts_map, pure_map)),
                rhs: Box::new(rewrite_calls_to_aborts_inner(rhs, aborts_map, pure_map)),
            }
        }

        // UnOp nodes
        IRNode::UnOp { op, operand } => {
            IRNode::UnOp {
                op: *op,
                operand: Box::new(rewrite_calls_to_aborts_inner(operand, aborts_map, pure_map)),
            }
        }

        // Pack nodes
        IRNode::Pack { struct_id, type_args, fields } => {
            IRNode::Pack {
                struct_id: *struct_id,
                type_args: type_args.clone(),
                fields: fields.iter().map(|f| rewrite_calls_to_aborts_inner(f, aborts_map, pure_map)).collect(),
            }
        }

        // Field nodes
        IRNode::Field { base, struct_id, field_index } => {
            IRNode::Field {
                base: Box::new(rewrite_calls_to_aborts_inner(base, aborts_map, pure_map)),
                struct_id: *struct_id,
                field_index: *field_index,
            }
        }

        // Unpack nodes
        IRNode::Unpack { struct_id, value } => {
            IRNode::Unpack {
                struct_id: *struct_id,
                value: Box::new(rewrite_calls_to_aborts_inner(value, aborts_map, pure_map)),
            }
        }

        // Tuple nodes
        IRNode::Tuple(elems) => {
            IRNode::Tuple(elems.iter().map(|e| rewrite_calls_to_aborts_inner(e, aborts_map, pure_map)).collect())
        }

        // VecOp nodes
        IRNode::VecOp { op, args } => {
            IRNode::VecOp {
                op: *op,
                args: args.iter().map(|a| rewrite_calls_to_aborts_inner(a, aborts_map, pure_map)).collect(),
            }
        }

        // UpdateField nodes
        IRNode::UpdateField { base, struct_id, field_index, value } => {
            IRNode::UpdateField {
                base: Box::new(rewrite_calls_to_aborts_inner(base, aborts_map, pure_map)),
                struct_id: *struct_id,
                field_index: *field_index,
                value: Box::new(rewrite_calls_to_aborts_inner(value, aborts_map, pure_map)),
            }
        }

        // UpdateVec nodes
        IRNode::UpdateVec { base, index, value } => {
            IRNode::UpdateVec {
                base: Box::new(rewrite_calls_to_aborts_inner(base, aborts_map, pure_map)),
                index: Box::new(rewrite_calls_to_aborts_inner(index, aborts_map, pure_map)),
                value: Box::new(rewrite_calls_to_aborts_inner(value, aborts_map, pure_map)),
            }
        }

        // While nodes
        IRNode::While { cond, body, vars } => {
            IRNode::While {
                cond: Box::new(rewrite_calls_to_aborts_inner(cond, aborts_map, pure_map)),
                body: Box::new(rewrite_calls_to_aborts_inner(body, aborts_map, pure_map)),
                vars: vars.clone(),
            }
        }

        // Return nodes
        IRNode::Return(values) => {
            IRNode::Return(values.iter().map(|v| rewrite_calls_to_aborts_inner(v, aborts_map, pure_map)).collect())
        }

        // Abort nodes
        IRNode::Abort(code) => {
            IRNode::Abort(Box::new(rewrite_calls_to_aborts_inner(code, aborts_map, pure_map)))
        }

        // Requires/Ensures nodes
        IRNode::Requires(cond) => {
            IRNode::Requires(Box::new(rewrite_calls_to_aborts_inner(cond, aborts_map, pure_map)))
        }

        IRNode::Ensures(cond) => {
            IRNode::Ensures(Box::new(rewrite_calls_to_aborts_inner(cond, aborts_map, pure_map)))
        }
    }
}

/// Rewrite function calls to use .pure variants and add proof arguments
fn rewrite_calls_to_pure(node: &IRNode, pure_map: &BTreeMap<FunctionID, FunctionID>) -> IRNode {
    node.clone().map(&mut |n| match n {
        IRNode::Call { function, type_args, mut args } => {
            // Replace with .pure variant if it exists
            let new_function = *pure_map.get(&function).unwrap_or(&function);

            // Add proof argument (placeholder) for .pure calls
            if pure_map.contains_key(&function) {
                // TODO: Generate actual proof from aborts predicate
                // For now, use a placeholder variable that will be rendered as "sorry"
                args.push(IRNode::Var("$proof".to_string()));
            }

            IRNode::Call {
                function: new_function,
                type_args,
                args,
            }
        }
        other => other,
    })
}
