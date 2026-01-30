// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Insert ToBool coercions at boundaries where Bool is required.
//!
//! In Lean, comparison operators (<, <=, >, >=) return `Prop`, not `Bool`.
//! However, `if` expressions require `Bool` conditions (or Decidable Props).
//!
//! This pass inserts `ToBool` wrappers around:
//! - If conditions that are comparisons (which return Prop)
//! - While conditions that are comparisons
//!
//! This pass should run after the main translation but before rendering.

use crate::data::functions::FunctionVariant;
use crate::data::Program;
use crate::{BinOp, IRNode};

/// Insert ToBool coercions in all runtime functions.
///
/// Runtime functions use `if` statements which require Bool conditions,
/// but comparisons return Prop in Lean. This pass wraps comparison-based
/// conditions with ToBool.
///
/// Aborts functions return Prop and don't need this transformation.
pub fn insert_bool_coercions(program: &mut Program) {
    // Collect function IDs that need transformation
    let function_ids: Vec<_> = program
        .functions
        .iter_ids()
        .filter(|func_id| {
            // Skip aborts functions - they use Prop throughout
            if func_id.variant == FunctionVariant::Aborts {
                return false;
            }
            // Skip spec variants (Requires, Ensures, etc.) - they also use Prop
            if func_id.variant.is_spec_variant() {
                return false;
            }
            // Skip native functions (no body - body will be IRNode::Tuple([]))
            let func = program.functions.get(func_id);
            if func.is_native() {
                return false;
            }
            true
        })
        .collect();

    for func_id in function_ids {
        let func = program.functions.get_mut(func_id);

        // Transform the function body using map()
        let body = std::mem::replace(&mut func.body, IRNode::unit());
        func.body = insert_coercions_in_node(body);
    }
}

/// Recursively insert ToBool coercions in If/While conditions.
/// Uses the functional map() API for recursive transformation.
fn insert_coercions_in_node(node: IRNode) -> IRNode {
    // Use map() for bottom-up transformation, then handle If/While conditions
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Ensure condition is Bool - wrap with ToBool if it's a Prop-returning expression
            let cond = ensure_bool_condition(*cond);
            IRNode::If {
                cond: Box::new(cond),
                then_branch,
                else_branch,
            }
        }

        IRNode::While {
            cond,
            body,
            vars,
            invariants,
        } => {
            // Ensure condition is Bool - wrap with ToBool if it's a Prop-returning expression
            let cond = ensure_bool_condition(*cond);
            IRNode::While {
                cond: Box::new(cond),
                body,
                vars,
                invariants,
            }
        }

        // All other nodes pass through unchanged (children already transformed by map())
        other => other,
    })
}

/// Ensure a condition expression produces Bool.
/// If the expression returns Prop (comparisons), wrap it with ToBool.
fn ensure_bool_condition(cond: IRNode) -> IRNode {
    // If it's already a ToBool, don't double-wrap
    if matches!(cond, IRNode::ToBool(_)) {
        return cond;
    }

    // Check if this expression returns Prop
    if returns_prop(&cond) {
        IRNode::ToBool(Box::new(cond))
    } else {
        cond
    }
}

/// Check if an expression returns Prop (as opposed to Bool).
/// Comparisons (<, <=, >, >=) return Prop in Lean.
/// Equality (==, !=) returns Bool via BEq typeclass.
fn returns_prop(node: &IRNode) -> bool {
    match node {
        // Comparison operators return Prop
        // Logical operators (And, Or) with Prop operands also return Prop
        IRNode::BinOp { op, lhs, rhs } => {
            if op.is_comparison() {
                true
            } else if matches!(op, BinOp::And | BinOp::Or) {
                returns_prop(lhs) || returns_prop(rhs)
            } else {
                false
            }
        }

        // ToProp explicitly creates a Prop
        IRNode::ToProp(_) => true,

        // Variables might be Prop - we can't tell without type context
        // For safety, assume they're Bool unless we know otherwise
        IRNode::Var(_) => false,

        // Everything else returns Bool or some other type
        _ => false,
    }
}
