// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates goal/proof obligation IR functions.
//!
//! For functions that have specs targeting them, this pass creates `.goal` variants
//! that express the proof obligation.
//!
//! The goal body depends on whether the spec has an error bound:
//! - With error bound: `ErrorBoundHolds impl(args).val spec(args).val bound(args).val`
//! - Without error bound: `to_spec(impl(args)) = spec(args)`
//!
//! Where:
//! - `impl` is the implementation function (separate from spec)
//! - `spec` is the spec function (separate from impl)
//! - `bound` is the error bound function (if present)
//! - `to_spec` is a type conversion function (e.g., i32_to_int) when types differ

use crate::data::functions::{FunctionID, FunctionVariant};
use crate::data::Program;
use crate::{BinOp, IRNode, Type};

/// Generate goal functions for all functions that have specs
pub fn generate_goal_functions(program: &mut Program) {
    // Build target->spec mapping
    let target_to_spec = program.build_target_to_spec_mapping();

    // Collect functions that need goals (have specs targeting them)
    let targets_with_specs: Vec<usize> = target_to_spec.keys().copied().collect();

    for target_id in targets_with_specs {
        let func_id = FunctionID::new(target_id);
        let func = program.functions.get(&func_id);

        // Note: We no longer skip native functions here because some functions
        // that are spec targets may be stubs (marked native) for functions
        // that couldn't be translated (e.g., functions with while loops).
        // The goal will reference the spec function and error bound, which is valid.

        // Get the spec function ID
        let spec_id = match target_to_spec.get(&target_id) {
            Some(id) => *id,
            None => continue,
        };

        // Build the goal body: to_spec(impl(args)) = spec(args)
        // Conversion functions are inserted automatically when types differ
        let goal_body = build_goal_body(program, target_id, spec_id);

        // Create the goal variant - returns Prop (logical proposition)
        program.create_variant(func_id, FunctionVariant::Goal, Type::Prop, |_| {
            goal_body.clone()
        });
    }
}

/// Build the goal body.
///
/// If the spec has an error bound, builds: `ErrorBoundHolds impl(args).val spec(args).val bound(args).val`
/// If the spec has ensures clauses, builds: `ensures(args) ∧ ensures_1(args) ∧ ...`
/// Otherwise builds: `impl(args) = spec(args)` (with type conversions as needed)
fn build_goal_body(program: &Program, target_id: usize, spec_id: usize) -> IRNode {
    let target_func = program.functions.get(&FunctionID::new(target_id));
    let spec_func = program.functions.get(&FunctionID::new(spec_id));

    // Build argument list from function parameters
    // For the impl call, use the target function's parameters
    let impl_args: Vec<IRNode> = target_func
        .signature
        .parameters
        .iter()
        .map(|p| IRNode::Var(p.name.clone()))
        .collect();

    // For the spec call, convert arguments if needed
    // The spec function's parameters may have different types (e.g., Int instead of I32)
    let spec_args: Vec<IRNode> = target_func
        .signature
        .parameters
        .iter()
        .zip(&spec_func.signature.parameters)
        .map(|(impl_param, spec_param)| {
            let arg = IRNode::Var(impl_param.name.clone());
            // If the types differ, insert a conversion call
            if impl_param.param_type != spec_param.param_type {
                if let Some(to_spec_fn) = program.conversions.to_spec_fn(&impl_param.param_type) {
                    IRNode::Call {
                        function: to_spec_fn,
                        type_args: vec![],
                        args: vec![arg],
                    }
                } else {
                    // No conversion available - just use the arg as-is
                    arg
                }
            } else {
                arg
            }
        })
        .collect();

    // Get type args (empty for non-generic functions)
    let type_args = target_func
        .signature
        .type_params
        .iter()
        .enumerate()
        .map(|(i, _)| Type::TypeParameter(i as u16))
        .collect::<Vec<_>>();

    // The impl call - use Runtime variant (impls call impls)
    let impl_call = IRNode::Call {
        function: FunctionID::new(target_id),
        type_args: type_args.clone(),
        args: impl_args,
    };

    // The spec call - call the spec function with converted arguments
    let spec_call = IRNode::Call {
        function: FunctionID::new(spec_id),
        type_args: type_args.clone(),
        args: spec_args.clone(),
    };

    // Check if the spec has an error bound variant
    let has_error_bound = program
        .functions
        .try_get(&FunctionID::with_variant(
            spec_id,
            FunctionVariant::ErrorBound,
        ))
        .is_some();

    // Count ensures variants
    let mut ensures_count = 0;
    while program
        .functions
        .try_get(&FunctionID::with_variant(
            spec_id,
            FunctionVariant::Ensures(ensures_count),
        ))
        .is_some()
    {
        ensures_count += 1;
    }

    // Check if the target has requires
    // IMPORTANT: The .requires variant is created for the SPEC function, not the target.
    // So we check spec_id for requires, but when we call it in the goal, we need to
    // use the proper function name (which will be rendered correctly by the backend).
    let has_requires = program
        .functions
        .try_get(&FunctionID::with_variant(
            spec_id,
            FunctionVariant::Requires,
        ))
        .is_some();

    // Build the core goal
    // Priority: 1) error bound, 2) ensures clauses, 3) equality
    let core_goal = if has_error_bound {
        // Build: ErrorBoundHolds impl(args) spec(args) bound(args)
        let bound_call = IRNode::Call {
            function: FunctionID::with_variant(spec_id, FunctionVariant::ErrorBound),
            type_args: type_args.clone(),
            args: spec_args.clone(),
        };

        IRNode::ErrorBoundGoal {
            impl_expr: Box::new(impl_call),
            spec_expr: Box::new(spec_call),
            bound_expr: Box::new(bound_call),
        }
    } else if ensures_count > 0 {
        // Build: ensures(args) ∧ ensures_1(args) ∧ ...
        // The ensures predicates take converted spec arguments
        let mut ensures_conjunction: Option<IRNode> = None;

        for i in 0..ensures_count {
            let ensures_call = IRNode::Call {
                function: FunctionID::with_variant(spec_id, FunctionVariant::Ensures(i)),
                type_args: type_args.clone(),
                args: spec_args.clone(),
            };

            ensures_conjunction = Some(match ensures_conjunction {
                None => ensures_call,
                Some(prev) => IRNode::BinOp {
                    op: BinOp::And,
                    lhs: Box::new(prev),
                    rhs: Box::new(ensures_call),
                },
            });
        }

        ensures_conjunction.unwrap_or_else(|| IRNode::Const(crate::Const::Bool(true)))
    } else {
        // Build: to_impl(impl(impl_args)) = spec(spec_args)
        // Or if types match: impl(impl_args) = spec(spec_args)
        let impl_result = impl_call;
        let spec_result = spec_call;

        // Convert the impl result to spec type if needed
        // NOTE: Impl functions have Except stripped when rendered, so we need to
        // compare and convert based on the INNER type, not the wrapped type.
        // Also, spec functions may have Except wrapping that needs to be ignored for comparison.
        let impl_inner_type = target_func.signature.return_type.base_type();
        let spec_inner_type = spec_func.signature.return_type.base_type();

        let converted_impl_result = if impl_inner_type != spec_inner_type {
            eprintln!(
                "[GOAL_GEN] Types differ for {}: impl_inner={:?} spec_inner={:?}",
                target_func.name, impl_inner_type, spec_inner_type
            );
            // Look up conversion for the inner type (without Except wrapper)
            if let Some(to_spec_fn) = program.conversions.to_spec_fn(&impl_inner_type) {
                eprintln!("[GOAL_GEN] Found conversion function for impl return type");
                IRNode::Call {
                    function: to_spec_fn,
                    type_args: vec![],
                    args: vec![impl_result],
                }
            } else {
                eprintln!("[GOAL_GEN] No conversion found for impl return type");
                // No conversion available
                impl_result
            }
        } else {
            impl_result
        };

        // Check if the spec function returns Except but impl doesn't (in rendered form)
        // In rendered Lean code:
        // - Impl functions (no spec_target) have Except stripped
        // - Spec functions (with spec_target) keep Except (wrapped with pure)
        // So if spec returns Except and impl doesn't have spec_target, we need
        // to wrap impl result with Pure to match types
        let spec_returns_except = spec_func.signature.return_type.is_monad();
        let impl_has_spec_target = target_func.spec_target.is_some();

        let final_impl_result = if spec_returns_except && !impl_has_spec_target {
            // Wrap impl result with Pure to match spec's Except type
            IRNode::Pure(Box::new(converted_impl_result))
        } else {
            converted_impl_result
        };

        IRNode::BinOp {
            op: BinOp::Eq,
            lhs: Box::new(final_impl_result),
            rhs: Box::new(spec_result),
        }
    };

    if has_requires {
        // Build: ¬requires(spec_args) ∨ core_goal
        // This is equivalent to: requires(spec_args) → core_goal
        //
        // Use spec_id for the requires call - the .requires variant is created
        // for the spec function, and it will be rendered with the target's name by the backend
        let requires_call = IRNode::Call {
            function: FunctionID::with_variant(spec_id, FunctionVariant::Requires),
            type_args,
            args: spec_args,
        };

        // ¬requires ∨ core_goal = requires → core_goal
        let not_requires = IRNode::UnOp {
            op: crate::UnOp::Not,
            operand: Box::new(requires_call),
        };

        IRNode::BinOp {
            op: BinOp::Or,
            lhs: Box::new(not_requires),
            rhs: Box::new(core_goal),
        }
    } else {
        core_goal
    }
}
