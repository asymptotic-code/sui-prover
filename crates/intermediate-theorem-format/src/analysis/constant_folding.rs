// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Constant folding pass for IR expressions.
//!
//! This pass evaluates expressions with constant arguments at compile time:
//! - Function calls where all arguments are constants (inlines the function body)
//! - Binary operations on constants
//! - Unary operations on constants
//! - Bit operations on constants
//! - If expressions with constant conditions

use crate::data::FunctionID;
use crate::{BinOp, BitOp, Const, IRNode, UnOp};
use ethnum::U256;
use std::collections::BTreeMap;

/// Function info for inlining: (parameter_names, body, is_native)
pub type FunctionBodies = BTreeMap<FunctionID, (Vec<String>, IRNode, bool)>;

/// Fold constants in an IR expression, inlining function calls where possible.
pub fn fold_constants(node: IRNode, function_bodies: &FunctionBodies) -> IRNode {
    // Use map to process bottom-up, so inner expressions are folded first
    node.map(&mut |n| fold_node(n, function_bodies))
}

/// Fold a single node
fn fold_node(node: IRNode, function_bodies: &FunctionBodies) -> IRNode {
    match node {
        // Inline function calls with all-constant arguments
        IRNode::Call { function, args, type_args } => {
            // Check if all arguments are constants
            if args.iter().all(|a| matches!(a, IRNode::Const(_))) {
                // Try to inline the function
                if let Some((params, body, is_native)) = function_bodies.get(&function) {
                    // Don't inline native functions
                    if *is_native {
                        return IRNode::Call { function, args, type_args };
                    }
                    // Substitute parameters with constant arguments
                    let mut result = body.clone();
                    for (param, arg) in params.iter().zip(args.iter()) {
                        result = substitute_var(&result, param, arg);
                    }
                    // Recursively fold the inlined body
                    return fold_constants(result, function_bodies);
                }
            }
            // Can't inline - return as-is
            IRNode::Call { function, args, type_args }
        }

        // Fold binary operations on constants
        IRNode::BinOp { op, lhs, rhs } => {
            if let (IRNode::Const(c1), IRNode::Const(c2)) = (&*lhs, &*rhs) {
                if let Some(result) = fold_binop(op, c1, c2) {
                    return IRNode::Const(result);
                }
            }
            IRNode::BinOp { op, lhs, rhs }
        }

        // Fold unary operations on constants
        IRNode::UnOp { op, operand } => {
            if let IRNode::Const(c) = &*operand {
                if let Some(result) = fold_unop(op, c) {
                    return IRNode::Const(result);
                }
            }
            IRNode::UnOp { op, operand }
        }

        // Fold bit operations on constants
        IRNode::BitOp(bit_op) => {
            if let Some(result) = fold_bitop(&bit_op) {
                return IRNode::Const(result);
            }
            IRNode::BitOp(bit_op)
        }

        // Fold if expressions with constant conditions
        IRNode::If { cond, then_branch, else_branch } => {
            if let IRNode::Const(Const::Bool(b)) = &*cond {
                return if *b { *then_branch } else { *else_branch };
            }
            IRNode::If { cond, then_branch, else_branch }
        }

        // Unwrap single-value Return nodes
        IRNode::Return(values) if values.len() == 1 => {
            values.into_iter().next().unwrap()
        }

        // Everything else passes through
        other => other,
    }
}

/// Substitute a variable name with a value in an IR tree
fn substitute_var(node: &IRNode, var_name: &str, value: &IRNode) -> IRNode {
    node.clone().map(&mut |n| {
        if let IRNode::Var(name) = &n {
            if name == var_name {
                return value.clone();
            }
        }
        n
    })
}

/// Mask a U256 value to fit in the given number of bits
fn mask_to_bits(value: U256, bits: usize) -> U256 {
    if bits >= 256 {
        value
    } else {
        value & ((U256::from(1u8) << bits) - 1)
    }
}

/// Try to fold a binary operation on two constants
fn fold_binop(op: BinOp, lhs: &Const, rhs: &Const) -> Option<Const> {
    match (op, lhs, rhs) {
        // Boolean operations
        (BinOp::And, Const::Bool(a), Const::Bool(b)) => Some(Const::Bool(*a && *b)),
        (BinOp::Or, Const::Bool(a), Const::Bool(b)) => Some(Const::Bool(*a || *b)),
        (BinOp::Eq, Const::Bool(a), Const::Bool(b)) => Some(Const::Bool(a == b)),
        (BinOp::Neq, Const::Bool(a), Const::Bool(b)) => Some(Const::Bool(a != b)),

        // Integer comparisons (works across different bit widths)
        (BinOp::Gt, Const::UInt { value: v1, .. }, Const::UInt { value: v2, .. }) => {
            Some(Const::Bool(v1 > v2))
        }
        (BinOp::Ge, Const::UInt { value: v1, .. }, Const::UInt { value: v2, .. }) => {
            Some(Const::Bool(v1 >= v2))
        }
        (BinOp::Lt, Const::UInt { value: v1, .. }, Const::UInt { value: v2, .. }) => {
            Some(Const::Bool(v1 < v2))
        }
        (BinOp::Le, Const::UInt { value: v1, .. }, Const::UInt { value: v2, .. }) => {
            Some(Const::Bool(v1 <= v2))
        }
        (BinOp::Eq, Const::UInt { value: v1, .. }, Const::UInt { value: v2, .. }) => {
            Some(Const::Bool(v1 == v2))
        }
        (BinOp::Neq, Const::UInt { value: v1, .. }, Const::UInt { value: v2, .. }) => {
            Some(Const::Bool(v1 != v2))
        }

        // Integer arithmetic (result uses larger bit width, masked appropriately)
        (BinOp::Add, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            let bits = (*b1).max(*b2);
            Some(Const::UInt { bits, value: mask_to_bits(v1.wrapping_add(*v2), bits) })
        }
        (BinOp::Sub, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            let bits = (*b1).max(*b2);
            Some(Const::UInt { bits, value: mask_to_bits(v1.wrapping_sub(*v2), bits) })
        }
        (BinOp::Mul, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            let bits = (*b1).max(*b2);
            Some(Const::UInt { bits, value: mask_to_bits(v1.wrapping_mul(*v2), bits) })
        }
        (BinOp::Div, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            if *v2 == U256::ZERO {
                None // Division by zero - don't fold
            } else {
                let bits = (*b1).max(*b2);
                Some(Const::UInt { bits, value: v1 / v2 })
            }
        }
        (BinOp::Mod, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            if *v2 == U256::ZERO {
                None // Modulo by zero - don't fold
            } else {
                let bits = (*b1).max(*b2);
                Some(Const::UInt { bits, value: v1 % v2 })
            }
        }

        // Bitwise operations
        (BinOp::BitAnd, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            let bits = (*b1).max(*b2);
            Some(Const::UInt { bits, value: v1 & v2 })
        }
        (BinOp::BitOr, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            let bits = (*b1).max(*b2);
            Some(Const::UInt { bits, value: v1 | v2 })
        }
        (BinOp::BitXor, Const::UInt { bits: b1, value: v1 }, Const::UInt { bits: b2, value: v2 }) => {
            let bits = (*b1).max(*b2);
            Some(Const::UInt { bits, value: v1 ^ v2 })
        }
        (BinOp::Shl, Const::UInt { bits, value }, Const::UInt { value: shift, .. }) => {
            let shift_amount = (*shift).min(U256::from(255u8));
            Some(Const::UInt {
                bits: *bits,
                value: mask_to_bits(*value << shift_amount, *bits)
            })
        }
        (BinOp::Shr, Const::UInt { bits, value }, Const::UInt { value: shift, .. }) => {
            let shift_amount = (*shift).min(U256::from(255u8));
            Some(Const::UInt { bits: *bits, value: *value >> shift_amount })
        }

        _ => None,
    }
}

/// Try to fold a unary operation on a constant
fn fold_unop(op: UnOp, operand: &Const) -> Option<Const> {
    match (op, operand) {
        // Boolean not
        (UnOp::Not, Const::Bool(b)) => Some(Const::Bool(!b)),

        // Bitwise not
        (UnOp::BitNot, Const::UInt { bits, value }) => {
            Some(Const::UInt { bits: *bits, value: mask_to_bits(!*value, *bits) })
        }

        // Type casts
        (UnOp::Cast(target_bits), Const::UInt { value, .. }) => {
            Some(Const::UInt {
                bits: target_bits as usize,
                value: if target_bits == 256 { *value } else { mask_to_bits(*value, target_bits as usize) }
            })
        }

        // Cast bool to int
        (UnOp::Cast(target_bits), Const::Bool(b)) => {
            Some(Const::UInt {
                bits: target_bits as usize,
                value: if *b { U256::from(1u8) } else { U256::ZERO }
            })
        }

        _ => None,
    }
}

/// Try to fold a bit operation on constants
fn fold_bitop(bit_op: &BitOp) -> Option<Const> {
    match bit_op {
        BitOp::Extract { high, low, operand } => {
            if let IRNode::Const(Const::UInt { value, .. }) = operand.as_ref() {
                let width = high - low + 1;
                let shifted = *value >> *low;
                let mask = (U256::from(1u8) << width) - 1;
                Some(Const::UInt { bits: width as usize, value: shifted & mask })
            } else {
                None
            }
        }
        BitOp::Concat { high, low } => {
            if let (
                IRNode::Const(Const::UInt { bits: high_bits, value: high_val }),
                IRNode::Const(Const::UInt { bits: low_bits, value: low_val })
            ) = (high.as_ref(), low.as_ref()) {
                let result = (*high_val << *low_bits) | *low_val;
                Some(Const::UInt { bits: high_bits + low_bits, value: result })
            } else {
                None
            }
        }
        BitOp::ZeroExtend { bits, operand } => {
            if let IRNode::Const(Const::UInt { bits: orig_bits, value }) = operand.as_ref() {
                // Zero extension just increases the bit width
                Some(Const::UInt { bits: orig_bits + (*bits as usize), value: *value })
            } else {
                None
            }
        }
        BitOp::SignExtend { bits, operand } => {
            if let IRNode::Const(Const::UInt { bits: orig_bits, value }) = operand.as_ref() {
                let new_bits = orig_bits + (*bits as usize);
                // Check sign bit
                let sign_bit = U256::from(1u8) << (orig_bits - 1);
                if *value & sign_bit != U256::ZERO {
                    // Negative - fill upper bits with 1s
                    let extension_mask = ((U256::from(1u8) << *bits) - 1) << orig_bits;
                    Some(Const::UInt { bits: new_bits, value: *value | extension_mask })
                } else {
                    // Positive - same as zero extension
                    Some(Const::UInt { bits: new_bits, value: *value })
                }
            } else {
                None
            }
        }
    }
}
