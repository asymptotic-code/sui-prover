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

        // Transform the function body
        let body = std::mem::replace(&mut func.body, IRNode::unit());
        func.body = insert_coercions_in_node(body);
    }
}

/// Recursively insert ToBool coercions in If/While conditions.
fn insert_coercions_in_node(node: IRNode) -> IRNode {
    match node {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Ensure condition is Bool - wrap with ToBool if it's a Prop-returning expression
            let cond = ensure_bool_condition(*cond);
            let then_branch = Box::new(insert_coercions_in_node(*then_branch));
            let else_branch = Box::new(insert_coercions_in_node(*else_branch));

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
            let body = Box::new(insert_coercions_in_node(*body));
            let invariants = invariants
                .into_iter()
                .map(insert_coercions_in_node)
                .collect();

            IRNode::While {
                cond: Box::new(cond),
                body,
                vars,
                invariants,
            }
        }

        IRNode::Block { children } => IRNode::Block {
            children: children.into_iter().map(insert_coercions_in_node).collect(),
        },

        IRNode::Let { pattern, value } => IRNode::Let {
            pattern,
            value: Box::new(insert_coercions_in_node(*value)),
        },

        IRNode::BinOp { op, lhs, rhs } => IRNode::BinOp {
            op,
            lhs: Box::new(insert_coercions_in_node(*lhs)),
            rhs: Box::new(insert_coercions_in_node(*rhs)),
        },

        IRNode::UnOp { op, operand } => IRNode::UnOp {
            op,
            operand: Box::new(insert_coercions_in_node(*operand)),
        },

        IRNode::Call {
            function,
            args,
            type_args,
        } => IRNode::Call {
            function,
            args: args.into_iter().map(insert_coercions_in_node).collect(),
            type_args,
        },

        IRNode::Tuple(elems) => {
            IRNode::Tuple(elems.into_iter().map(insert_coercions_in_node).collect())
        }

        IRNode::Pack {
            struct_id,
            type_args,
            fields,
        } => IRNode::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(insert_coercions_in_node).collect(),
        },

        IRNode::Field {
            base,
            struct_id,
            field_index,
        } => IRNode::Field {
            base: Box::new(insert_coercions_in_node(*base)),
            struct_id,
            field_index,
        },

        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => IRNode::UpdateField {
            base: Box::new(insert_coercions_in_node(*base)),
            struct_id,
            field_index,
            value: Box::new(insert_coercions_in_node(*value)),
        },

        IRNode::UpdateVec { base, index, value } => IRNode::UpdateVec {
            base: Box::new(insert_coercions_in_node(*base)),
            index: Box::new(insert_coercions_in_node(*index)),
            value: Box::new(insert_coercions_in_node(*value)),
        },

        IRNode::Return(values) => {
            IRNode::Return(values.into_iter().map(insert_coercions_in_node).collect())
        }

        IRNode::Abort(code) => IRNode::Abort(Box::new(insert_coercions_in_node(*code))),

        IRNode::Pure(inner) => IRNode::Pure(Box::new(insert_coercions_in_node(*inner))),

        IRNode::ToProp(inner) => IRNode::ToProp(Box::new(insert_coercions_in_node(*inner))),

        IRNode::ToBool(inner) => IRNode::ToBool(Box::new(insert_coercions_in_node(*inner))),

        // Leaf nodes - no transformation needed
        IRNode::Var(_)
        | IRNode::Const(_)
        | IRNode::Unpack { .. }
        | IRNode::WhileAborts { .. }
        | IRNode::Requires(_)
        | IRNode::Ensures(_)
        | IRNode::ErrorBound(_)
        | IRNode::ErrorBoundRelative { .. }
        | IRNode::ErrorBoundGoal { .. }
        | IRNode::BitOp(_) => node,
    }
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
