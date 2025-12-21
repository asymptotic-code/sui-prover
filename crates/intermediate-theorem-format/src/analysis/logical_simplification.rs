// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Logical simplification pass for IR expressions.
//!
//! This pass simplifies boolean and comparison expressions using algebraic rules.
//! It does NOT handle constant folding (that's in constant_folding.rs).
//!
//! Simplifications include:
//! - Double negation: ¬¬x → x
//! - Comparison negation: ¬(a == b) → a != b, ¬(a < b) → a >= b, etc.
//! - Boolean identity: true && x → x, false || x → x, etc.
//! - Conditional with identical branches: if c then x else x → x
//! - Conditional to boolean: if c then True else False → c

use crate::{BinOp, Const, IRNode, UnOp};

/// Simplify an IR expression while preserving structure.
pub fn simplify(ir: IRNode) -> IRNode {
    ir.map(&mut simplify_node)
}

/// Simplify a single IR node (called bottom-up by map)
fn simplify_node(node: IRNode) -> IRNode {
    match node {
        // Boolean negation simplifications
        IRNode::UnOp { op: UnOp::Not, operand } => simplify_not(*operand),

        // Binary operation simplifications
        IRNode::BinOp { op, lhs, rhs } => simplify_binop(op, *lhs, *rhs),

        // Conditional simplifications
        IRNode::If { cond, then_branch, else_branch } => {
            simplify_if(*cond, *then_branch, *else_branch)
        }

        // Everything else passes through
        other => other,
    }
}

/// Simplify negation expressions
fn simplify_not(inner: IRNode) -> IRNode {
    match inner {
        // ¬¬x → x
        IRNode::UnOp { op: UnOp::Not, operand } => *operand,

        // ¬(a != b) → a == b
        IRNode::BinOp { op: BinOp::Neq, lhs, rhs } => IRNode::BinOp {
            op: BinOp::Eq,
            lhs,
            rhs,
        },

        // ¬(a == b) → a != b
        IRNode::BinOp { op: BinOp::Eq, lhs, rhs } => IRNode::BinOp {
            op: BinOp::Neq,
            lhs,
            rhs,
        },

        // ¬(a < b) → a >= b
        IRNode::BinOp { op: BinOp::Lt, lhs, rhs } => IRNode::BinOp {
            op: BinOp::Ge,
            lhs,
            rhs,
        },

        // ¬(a <= b) → a > b
        IRNode::BinOp { op: BinOp::Le, lhs, rhs } => IRNode::BinOp {
            op: BinOp::Gt,
            lhs,
            rhs,
        },

        // ¬(a > b) → a <= b
        IRNode::BinOp { op: BinOp::Gt, lhs, rhs } => IRNode::BinOp {
            op: BinOp::Le,
            lhs,
            rhs,
        },

        // ¬(a >= b) → a < b
        IRNode::BinOp { op: BinOp::Ge, lhs, rhs } => IRNode::BinOp {
            op: BinOp::Lt,
            lhs,
            rhs,
        },

        // Otherwise keep the negation
        other => IRNode::UnOp {
            op: UnOp::Not,
            operand: Box::new(other),
        },
    }
}

/// Check if an expression always evaluates to a boolean constant.
/// This is used for simplifying logical operations where one operand
/// is known to be constant (e.g., `x || False` → `x`).
fn evaluates_to_bool(node: &IRNode) -> Option<bool> {
    match node {
        IRNode::Const(Const::Bool(b)) => Some(*b),
        // For a Block, the last expression is the result
        IRNode::Block { children } => children.last().and_then(evaluates_to_bool),
        // For If, if both branches evaluate to the same bool, the whole If does
        IRNode::If { then_branch, else_branch, .. } => {
            match (evaluates_to_bool(then_branch), evaluates_to_bool(else_branch)) {
                (Some(t), Some(e)) if t == e => Some(t),
                _ => None,
            }
        }
        // For negation, negate the inner result
        IRNode::UnOp { op: UnOp::Not, operand } => evaluates_to_bool(operand).map(|b| !b),
        // For And/Or with constant operands
        IRNode::BinOp { op: BinOp::And, lhs, rhs } => {
            match (evaluates_to_bool(lhs), evaluates_to_bool(rhs)) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            }
        }
        IRNode::BinOp { op: BinOp::Or, lhs, rhs } => {
            match (evaluates_to_bool(lhs), evaluates_to_bool(rhs)) {
                (Some(true), _) | (_, Some(true)) => Some(true),
                (Some(false), Some(false)) => Some(false),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Simplify binary operations using algebraic identities
fn simplify_binop(op: BinOp, lhs: IRNode, rhs: IRNode) -> IRNode {
    // Check if operands evaluate to constant bools (including through Let/Block)
    let lhs_bool = evaluates_to_bool(&lhs);
    let rhs_bool = evaluates_to_bool(&rhs);

    match (&op, lhs_bool, rhs_bool) {
        // true && x → x
        (BinOp::And, Some(true), _) => rhs,
        // x && true → x
        (BinOp::And, _, Some(true)) => lhs,
        // false && x → false
        (BinOp::And, Some(false), _) => IRNode::Const(Const::Bool(false)),
        // x && false → false
        (BinOp::And, _, Some(false)) => IRNode::Const(Const::Bool(false)),

        // true || x → true
        (BinOp::Or, Some(true), _) => IRNode::Const(Const::Bool(true)),
        // x || true → true
        (BinOp::Or, _, Some(true)) => IRNode::Const(Const::Bool(true)),
        // false || x → x
        (BinOp::Or, Some(false), _) => rhs,
        // x || false → x
        (BinOp::Or, _, Some(false)) => lhs,

        // Default: keep the operation
        _ => IRNode::BinOp {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
    }
}

/// Simplify if expressions
fn simplify_if(cond: IRNode, then_branch: IRNode, else_branch: IRNode) -> IRNode {
    match (&then_branch, &else_branch) {
        // if c then True else False → c
        (IRNode::Const(Const::Bool(true)), IRNode::Const(Const::Bool(false))) => cond,
        // if c then False else True → ¬c
        (IRNode::Const(Const::Bool(false)), IRNode::Const(Const::Bool(true))) => {
            IRNode::UnOp {
                op: UnOp::Not,
                operand: Box::new(cond),
            }
        }
        // if c then x else x → x (when branches are identical)
        _ if then_branch == else_branch => then_branch,
        // Otherwise keep the if
        _ => IRNode::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        },
    }
}
