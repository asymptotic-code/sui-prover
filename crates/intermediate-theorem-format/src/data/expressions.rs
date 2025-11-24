// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use crate::data::structure::TheoremStructID;
use crate::data::types::{TempId, TheoremType};
use crate::TheoremFunctionID;
use ethnum::U256;
use num::BigUint;
use serde::{Deserialize, Serialize};

/// Constant value that can represent various numeric types
#[derive(Debug, Clone)]
pub enum ConstantValue {
    /// Boolean value
    Bool(bool),
    /// Unsigned integer with specified bit width (8, 16, 32, 64, 128, or 256)
    /// Stored as U256 for uniform representation, with bits indicating the actual type
    UInt { bits: usize, value: U256 },
    /// Address (semantically distinct from generic integers)
    Address(BigUint),
    /// Vector of constants (handles arrays, byte arrays, etc.)
    Vector(Vec<ConstantValue>),
}

impl ConstantValue {
    /// Convert to string representation for Lean output
    pub fn to_string(&self) -> String {
        match self {
            ConstantValue::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            ConstantValue::UInt { value, .. } => value.to_string(),
            ConstantValue::Address(addr) => addr.to_string(),
            ConstantValue::Vector(elements) => format!("[{}]", elements
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<String>>()
                        .join(", "))
        }
    }
}

/// Specifies how to render the function call
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CallConvention {
    /// Pure call: f(x, y)
    Pure,
    /// Monadic call: do x ← f a b; ...
    Monadic,
}

/// SSA operation
#[derive(Debug, Clone)]
pub enum Expression {
    /// Temporary value
    Temporary(TempId),

    /// Constant value (supports U128, U256, and arbitrary precision)
    Constant(ConstantValue),

    /// Binary operation
    BinOp {
        op: BinOp,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },

    /// Unary operation
    UnOp {
        op: UnOp,
        operand: Box<Expression>,
    },

    /// Cast operation
    Cast {
        value: Box<Expression>,
        target_type: TheoremType,
    },

    /// Function call
    Call {
        function: TheoremFunctionID,
        args: Vec<Expression>,
        type_args: Vec<TheoremType>,
        convention: CallConvention,
    },

    /// Pack (create struct)
    Pack {
        struct_id: TheoremStructID,
        fields: Vec<Expression>,
    },

    /// Unpack single field (destructure struct - extract one field)
    Unpack {
        struct_id: TheoremStructID,
        field_index: usize,
        operand: Box<Expression>,
    },

    /// Unpack all fields (destructure struct - extract all fields as tuple)
    /// Used for multi-result Let statements
    UnpackAll {
        struct_id: TheoremStructID,
        operand: Box<Expression>,
    },

    /// Vector operation
    VecOp {
        op: VectorOp,
        operands: Vec<Expression>,
    },
}

/// Binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    BitAnd, BitOr, BitXor, Shl, Shr,
    And, Or,
    Eq, Neq, Lt, Le, Gt, Ge,
}

/// Unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnOp {
    Not,
    CastU8,
    CastU16,
    CastU32,
    CastU64,
    CastU128,
    CastU256,
}

/// Vector operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VectorOp {
    Empty,
    Length,
    Push,
    Pop,
    Borrow,
    BorrowMut,
    Swap,
}

impl Expression {
    /// Extract function ID if this is a Call expression
    pub fn called_function(&self) -> Option<TheoremFunctionID> {
        match self {
            Expression::Call { function, .. } => Some(*function),
            _ => None,
        }
    }

    /// Extract struct ID if this is a Pack or Unpack expression
    pub fn struct_reference(&self) -> Option<TheoremStructID> {
        match self {
            Expression::Pack { struct_id, .. }
            | Expression::Unpack { struct_id, .. }
            | Expression::UnpackAll { struct_id, .. } => Some(*struct_id),
            _ => None,
        }
    }

    /// Collect all struct IDs from types in this expression
    pub fn collect_type_struct_ids(&self) -> Vec<TheoremStructID> {
        let mut result = Vec::new();
        match self {
            Expression::Cast { target_type, .. } => {
                result.extend(target_type.collect_struct_ids());
            }
            Expression::Call { type_args, .. } => {
                for ty in type_args {
                    result.extend(ty.collect_struct_ids());
                }
            }
            _ => {}
        }
        result
    }
}


