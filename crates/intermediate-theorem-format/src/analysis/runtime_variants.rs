// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Generates .aborts and .pure variants for all runtime functions
//!
//! For each non-spec, non-native monadic function, this pass generates:
//! - `.aborts` : Prop - predicate indicating when the function aborts
//! - `.pure` : non-monadic version that calls other .pure functions

use crate::data::functions::FunctionVariant;
use crate::data::Program;
use crate::{Const, FunctionID, IRNode, Type};
use std::collections::HashSet;

/// Generate .aborts and .pure variants for all runtime functions.
///
/// Prerequisites: `analyze_monadicity` must have run first to set return types.
pub fn generate_runtime_variants(program: &mut Program) {
    // Collect monadic runtime base function IDs (these will get Pure variants)
    let monadic_base_ids: HashSet<usize> = program
        .functions
        .iter()
        .filter(|(id, f)| id.is_runtime() && !f.is_spec() && !f.is_native() && f.is_monadic())
        .map(|(id, _)| id.base)
        .collect();

    // Generate variants for each monadic function
    for &base_id in &monadic_base_ids {
        let func_id = FunctionID::new(base_id);

        // Generate .aborts variant - calls to monadic functions rewritten to Pure
        program.create_variant(func_id, FunctionVariant::Aborts, Type::Bool, |body| {
            convert_to_aborts_predicate(body)
                .to_variant(FunctionVariant::Pure, |id| monadic_base_ids.contains(&id))
        });

        // Generate .pure variant - calls to monadic functions rewritten to Pure
        let return_type = program.functions.get(&func_id).signature.return_type.base_type();
        program.create_variant(func_id, FunctionVariant::Pure, return_type, |body| {
            convert_to_pure(body)
                .to_variant(FunctionVariant::Pure, |id| monadic_base_ids.contains(&id))
        });
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

/// Convert monadic IR to pure (non-monadic) version.
/// Simplify aborting ifs, filter out Abort nodes, and unwrap Returns.
fn convert_to_pure(node: &IRNode) -> IRNode {
    // First simplify If nodes where branches always abort
    let node = simplify_aborting_ifs(node.clone());

    // Filter out Abort nodes from blocks, unwrap Returns
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

/// Simplify If nodes where branches always abort.
/// - If both branches abort, replace with unit (unreachable)
/// - If only then branch aborts, keep else branch
/// - If only else branch aborts, keep then branch
fn simplify_aborting_ifs(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let then_always_aborts = then_branch.always_aborts();
            let else_always_aborts = else_branch.always_aborts();

            if then_always_aborts && else_always_aborts {
                IRNode::unit()
            } else if then_always_aborts {
                *else_branch
            } else if else_always_aborts {
                *then_branch
            } else {
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
        }
        other => other,
    })
}
