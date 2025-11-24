// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Shared utilities for translation
//!
//! Provides common functionality used across multiple translators:
//! - Constant value conversion
//! - Binary/unary operation mapping
//! - ID resolution (functions, structs)

use intermediate_theorem_format::{BinOp, UnOp, ConstantValue, TheoremFunctionID, TheoremStructID};
use move_stackless_bytecode::stackless_bytecode::{Constant, Operation};
use move_model::model::QualifiedId;

/// Convert Move constant to ConstantValue
pub fn convert_constant(constant: &Constant) -> ConstantValue {
    use ethnum::U256;

    match constant {
        Constant::Bool(b) => ConstantValue::Bool(*b),
        Constant::U8(v) => ConstantValue::UInt {
            bits: 8,
            value: U256::from(*v),
        },
        Constant::U16(v) => ConstantValue::UInt {
            bits: 16,
            value: U256::from(*v),
        },
        Constant::U32(v) => ConstantValue::UInt {
            bits: 32,
            value: U256::from(*v),
        },
        Constant::U64(v) => ConstantValue::UInt {
            bits: 64,
            value: U256::from(*v),
        },
        Constant::U128(v) => ConstantValue::UInt {
            bits: 128,
            value: U256::from(*v),
        },
        Constant::U256(v) => ConstantValue::UInt {
            bits: 256,
            value: *v,
        },
        Constant::Address(addr) => {
            ConstantValue::Address(addr.clone())
        }
        Constant::ByteArray(bytes) => {
            // Convert byte array to vector of U8 constants
            let elements: Vec<ConstantValue> = bytes
                .iter()
                .map(|&b| ConstantValue::UInt {
                    bits: 8,
                    value: U256::from(b),
                })
                .collect();
            ConstantValue::Vector(elements)
        }
        Constant::Vector(elements) => {
            // Recursively convert vector elements
            let converted: Vec<ConstantValue> = elements
                .iter()
                .map(|elem| convert_constant(elem))
                .collect();
            ConstantValue::Vector(converted)
        }
        Constant::AddressArray(addresses) => {
            // Convert address array to vector of addresses
            let converted: Vec<ConstantValue> = addresses
                .iter()
                .map(|addr| ConstantValue::Address(addr.clone()))
                .collect();
            ConstantValue::Vector(converted)
        }
    }
}

/// Convert Move binary operation to IR BinOp
pub fn convert_binop(op: &Operation) -> BinOp {
    match op {
        Operation::Add => BinOp::Add,
        Operation::Sub => BinOp::Sub,
        Operation::Mul => BinOp::Mul,
        Operation::Div => BinOp::Div,
        Operation::Mod => BinOp::Mod,
        Operation::BitAnd => BinOp::BitAnd,
        Operation::BitOr => BinOp::BitOr,
        Operation::Xor => BinOp::BitXor,
        Operation::Shl => BinOp::Shl,
        Operation::Shr => BinOp::Shr,
        Operation::And => BinOp::And,
        Operation::Or => BinOp::Or,
        Operation::Eq => BinOp::Eq,
        Operation::Neq => BinOp::Neq,
        Operation::Lt => BinOp::Lt,
        Operation::Le => BinOp::Le,
        Operation::Gt => BinOp::Gt,
        Operation::Ge => BinOp::Ge,
        _ => panic!("BUG: Unsupported operation {:?} in binary operation conversion", op),
    }
}

/// Convert Move unary operation to IR UnOp
pub fn convert_unop(op: &Operation) -> UnOp {
    match op {
        Operation::Not => UnOp::Not,
        _ => panic!("BUG: Unsupported operation {:?} in unary operation conversion", op),
    }
}

/// Resolve struct ID from Move module and datatype IDs
pub fn resolve_struct_id(
    builder: &mut crate::program_builder::ProgramBuilder,
    module_id: move_model::model::ModuleId,
    struct_id: move_model::model::DatatypeId,
) -> TheoremStructID {
    let qualified = QualifiedId { module_id, id: struct_id };
    builder.get_or_reserve_struct_id(qualified)
}

/// Resolve function ID from Move module and function IDs
pub fn resolve_function_id(
    builder: &mut crate::program_builder::ProgramBuilder,
    module_id: move_model::model::ModuleId,
    fun_id: move_model::model::FunId,
) -> TheoremFunctionID {
    let qualified = QualifiedId { module_id, id: fun_id };
    builder.get_or_reserve_function_id(qualified)
}
