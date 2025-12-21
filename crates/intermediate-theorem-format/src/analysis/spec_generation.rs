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
use crate::{BinOp, Const, IRNode, Type};
use std::collections::HashSet;

/// Generate requires/ensures functions for all spec functions
pub fn generate_spec_functions(program: &mut Program) {
    // Collect base IDs that have Pure variants (created by runtime_variants)
    // This must run AFTER generate_runtime_variants
    let has_pure_variant: HashSet<usize> = program
        .functions
        .iter()
        .filter(|(id, _)| id.variant == FunctionVariant::Pure)
        .map(|(id, _)| id.base)
        .collect();

    // Collect spec function IDs (only base/runtime variants)
    let spec_func_ids: Vec<_> = program
        .functions
        .iter()
        .filter(|(id, f)| id.is_runtime() && f.is_spec())
        .map(|(id, _)| id)
        .collect();

    for func_id in spec_func_ids {
        let func = program.functions.get(&func_id);

        // Count requires and ensures
        let requires_count = func.body.iter().filter(|n| matches!(n, IRNode::Requires(_))).count();
        let ensures_count = func.body.iter().filter(|n| matches!(n, IRNode::Ensures(_))).count();

        // Generate .requires variant if any requires exist
        // 1. Replace calls to target functions with their spec replacements
        // 2. Rewrite remaining calls to Pure variants where available
        if requires_count > 0 {
            program.create_variant(
                func_id,
                FunctionVariant::Requires,
                Type::Bool,
                |body| transform_spec_body(body, SpecExtract::Requires)
                    .to_variant(FunctionVariant::Pure, |id| has_pure_variant.contains(&id)),
            );
        }

        // Generate .ensures variants for each ensures clause
        for idx in 0..ensures_count {
            program.create_variant(
                func_id,
                FunctionVariant::Ensures(idx),
                Type::Bool,
                |body| transform_spec_body(body, SpecExtract::Ensures(idx))
                    .to_variant(FunctionVariant::Pure, |id| has_pure_variant.contains(&id)),
            );
        }
    }
}

/// What to extract from the spec function body
enum SpecExtract {
    Requires,
    Ensures(usize),
}

/// Transform spec function body to extract requires or ensures conditions
fn transform_spec_body(node: &IRNode, extract: SpecExtract) -> IRNode {
    let mut captured_vars = Vec::new();
    let mut ensures_counter = 0;

    // Transform: replace target nodes with let bindings, capturing the var names
    let transformed = node.clone().map(&mut |n| match (&extract, n) {
        (SpecExtract::Requires, IRNode::Requires(cond)) => {
            let var_name = format!("$requires_{}", captured_vars.len());
            captured_vars.push(var_name.clone());
            IRNode::Let {
                pattern: vec![var_name],
                value: cond,
            }
        }
        (SpecExtract::Ensures(target_idx), IRNode::Ensures(cond)) => {
            if ensures_counter == *target_idx {
                let var_name = format!("$ensures_{}", captured_vars.len());
                captured_vars.push(var_name.clone());
                ensures_counter += 1;
                IRNode::Let {
                    pattern: vec![var_name],
                    value: cond,
                }
            } else {
                ensures_counter += 1;
                IRNode::unit() // Will be filtered out
            }
        }
        (_, other) => other,
    });

    // Filter out the nodes we don't need
    let transformed = match extract {
        SpecExtract::Requires => {
            transformed.filter(|n| !matches!(n, IRNode::Ensures(_) | IRNode::Return(_)))
        }
        SpecExtract::Ensures(_) => {
            transformed.filter(|n| !matches!(n, IRNode::Requires(_) | IRNode::Ensures(_) | IRNode::Return(_)))
        }
    };

    // Filter out empty units
    let transformed = transformed.filter(|n| !matches!(n, IRNode::Tuple(v) if v.is_empty()));

    if captured_vars.is_empty() {
        return IRNode::Const(Const::Bool(true));
    }

    // Combine all captured conditions with AND
    let combined = combine_with_and(captured_vars.into_iter().map(IRNode::Var).collect());

    // Filter out non-Let expressions from the block since specs should only have
    // Let bindings followed by the final combined Prop condition.
    // This removes leftover expressions like variable references that remain
    // after filtering out Returns.
    let transformed = transformed.filter(|n| matches!(n, IRNode::Let { .. }));

    transformed.combine(combined)
}

/// Combine expressions with AND
fn combine_with_and(exprs: Vec<IRNode>) -> IRNode {
    exprs
        .into_iter()
        .reduce(|acc, expr| IRNode::BinOp {
            op: BinOp::And,
            lhs: Box::new(acc),
            rhs: Box::new(expr),
        })
        .unwrap_or(IRNode::Const(Const::Bool(true)))
}
