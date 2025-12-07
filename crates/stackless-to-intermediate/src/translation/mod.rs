// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translation utilities for Move bytecode to TheoremIR

use ethnum::U256;
use intermediate_theorem_format::{BinOp, Const, Type};
use move_stackless_bytecode::stackless_bytecode::{Constant, Operation};

pub(crate) mod function_translator;
pub(crate) mod ir_translator;

/// Convert a Move constant to IR Const.
/// The `expected_type` is used to determine the element type for empty vectors.
pub fn convert_constant(constant: &Constant, expected_type: &Type) -> Const {
    match constant {
        Constant::Bool(b) => Const::Bool(*b),
        Constant::U8(v) => Const::UInt {
            bits: 8,
            value: U256::from(*v),
        },
        Constant::U16(v) => Const::UInt {
            bits: 16,
            value: U256::from(*v),
        },
        Constant::U32(v) => Const::UInt {
            bits: 32,
            value: U256::from(*v),
        },
        Constant::U64(v) => Const::UInt {
            bits: 64,
            value: U256::from(*v),
        },
        Constant::U128(v) => Const::UInt {
            bits: 128,
            value: U256::from(*v),
        },
        Constant::U256(v) => Const::UInt {
            bits: 256,
            value: *v,
        },
        Constant::Address(addr) => Const::Address(addr.clone()),
        Constant::ByteArray(bytes) => Const::Vector {
            elem_type: Type::UInt(8),
            elems: bytes
                .iter()
                .map(|&b| Const::UInt {
                    bits: 8,
                    value: U256::from(b),
                })
                .collect(),
        },
        Constant::Vector(elements) => {
            // Get element type from expected_type (which should be Vector<T>)
            let elem_type = match expected_type {
                Type::Vector(inner) => inner.as_ref().clone(),
                _ => panic!("BUG: Expected vector type for vector constant, got {:?}", expected_type),
            };
            let elems = elements
                .iter()
                .map(|e| convert_constant(e, &elem_type))
                .collect();
            Const::Vector { elem_type, elems }
        }
        Constant::AddressArray(addresses) => Const::Vector {
            elem_type: Type::Address,
            elems: addresses
                .iter()
                .map(|addr| Const::Address(addr.clone()))
                .collect(),
        },
    }
}

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
        _ => panic!("BUG: Unsupported binary operation {:?}", op),
    }
}
