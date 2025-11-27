// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Expression translation from Move bytecode operations to TheoremIR expressions
//!
//! Single responsibility: Convert bytecode operations into Expression IR nodes.
//! Does NOT create Statement nodes - that's statement_translator's job.

use intermediate_theorem_format::{Expression, CallConvention, TheoremType, TempId};
use move_stackless_bytecode::stackless_bytecode::Operation;
use crate::program_builder::ProgramBuilder;
use super::utilities::{convert_constant, convert_binop, convert_unop, resolve_function_id};

/// Translate an operation to an expression
/// Returns None for operations that don't produce single-value expressions
pub fn translate_operation(
    builder: &mut ProgramBuilder,
    operation: &Operation,
    srcs: &[usize],
) -> Option<Expression> {
    match operation {
        // Binary operations
        Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod |
        Operation::BitOr | Operation::BitAnd | Operation::Xor | Operation::Shl | Operation::Shr |
        Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge | Operation::Or | Operation::And |
        Operation::Eq | Operation::Neq => {
            if srcs.len() != 2 {
                panic!("BUG: Binary operation with {} operands", srcs.len());
            }
            let bin_op = convert_binop(operation);
            Some(Expression::BinOp {
                op: bin_op,
                lhs: Box::new(Expression::Temporary(srcs[0] as TempId)),
                rhs: Box::new(Expression::Temporary(srcs[1] as TempId)),
            })
        }

        // Unary operations
        Operation::Not => {
            if srcs.len() != 1 {
                panic!("BUG: Unary operation with {} operands", srcs.len());
            }
            Some(Expression::UnOp {
                op: convert_unop(operation),
                operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
            })
        }

        // Cast operations
        Operation::CastU8 | Operation::CastU16 | Operation::CastU32 |
        Operation::CastU64 | Operation::CastU128 | Operation::CastU256 => {
            if srcs.len() != 1 {
                panic!("BUG: Cast operation with {} operands", srcs.len());
            }
            let target_type = match operation {
                Operation::CastU8 => TheoremType::UInt(8),
                Operation::CastU16 => TheoremType::UInt(16),
                Operation::CastU32 => TheoremType::UInt(32),
                Operation::CastU64 => TheoremType::UInt(64),
                Operation::CastU128 => TheoremType::UInt(128),
                Operation::CastU256 => TheoremType::UInt(256),
                _ => unreachable!(),
            };
            Some(Expression::Cast {
                value: Box::new(Expression::Temporary(srcs[0] as TempId)),
                target_type,
            })
        }

        // Pack: create struct
        Operation::Pack(module_id, struct_id, type_args) => {
            let qualified_id = module_id.qualified(*struct_id);
            let struct_id_ir = builder.get_or_reserve_struct_id(qualified_id);

            let fields = srcs.iter()
                .map(|&temp| Expression::Temporary(temp as TempId))
                .collect();

            let type_args_ir = type_args.iter()
                .map(|ty| builder.convert_type(ty))
                .collect();

            Some(Expression::Pack {
                struct_id: struct_id_ir,
                type_args: type_args_ir,
                fields,
            })
        }

        // PackVariant - treat like Pack
        Operation::PackVariant(module_id, struct_id, _variant_id, type_args) => {
            let qualified_id = module_id.qualified(*struct_id);
            let struct_id_ir = builder.get_or_reserve_struct_id(qualified_id);

            let fields = srcs.iter()
                .map(|&temp| Expression::Temporary(temp as TempId))
                .collect();

            let type_args_ir = type_args.iter()
                .map(|ty| builder.convert_type(ty))
                .collect();

            Some(Expression::Pack {
                struct_id: struct_id_ir,
                type_args: type_args_ir,
                fields,
            })
        }

        // Unpack operations - multi-result, handled by statement translator
        Operation::Unpack(..) | Operation::UnpackVariant(..) => None,

        // GetField: extract single field from struct
        Operation::GetField(module_id, struct_id, _type_args, field_idx) => {
            if srcs.is_empty() {
                panic!("BUG: GetField operation with no source");
            }

            let qualified_id = module_id.qualified(*struct_id);
            let struct_id_ir = builder.get_or_reserve_struct_id(qualified_id);

            Some(Expression::FieldAccess {
                struct_id: struct_id_ir,
                field_index: *field_idx,
                operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
            })
        }

        // BorrowField - extract field from struct
        Operation::BorrowField(module_id, struct_id, _type_args, field_index) => {
            if srcs.is_empty() {
                return None;
            }

            let qualified_id = module_id.qualified(*struct_id);

            // Get or create struct ID
            let struct_id_ir = builder.get_or_reserve_struct_id(qualified_id);

            Some(Expression::FieldAccess {
                struct_id: struct_id_ir,
                field_index: *field_index,
                operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
            })
        }

        // Reference operations - in value semantics, these are identity
        Operation::BorrowLoc | Operation::BorrowGlobal(..) | Operation::ReadRef | Operation::FreezeRef => {
            if srcs.is_empty() {
                return None;
            }
            Some(Expression::Temporary(srcs[0] as TempId))
        }

        // Function calls
        Operation::Function(module_id, fun_id, type_args) => {
            let function_id = resolve_function_id(builder, *module_id, *fun_id);

            let args = srcs.iter()
                .map(|&temp| Expression::Temporary(temp as TempId))
                .collect();
            let type_args_ir = type_args.iter()
                .map(|ty| builder.convert_type(ty))
                .collect();

            // Native functions are pure (don't return Except), all others are monadic
            let convention = if builder.is_function_native(*module_id, *fun_id) {
                CallConvention::Pure
            } else {
                CallConvention::Monadic
            };

            Some(Expression::Call {
                function: function_id,
                args,
                type_args: type_args_ir,
                convention,
            })
        }

        // Operations that don't produce expressions
        Operation::WriteRef | Operation::Destroy |
        Operation::GetGlobal(..) | Operation::MoveFrom(..) |
        Operation::MoveTo(..) | Operation::Exists(..) |
        Operation::TraceLocal(_) | Operation::TraceReturn(_) |
        Operation::TraceAbort | Operation::TraceExp(_, _) |
        Operation::TraceGlobalMem(_) | Operation::TraceGhost(_, _) => None,

        _ => panic!("BUG: Unsupported operation {:?} in expression translation", operation),
    }
}

/// Create a constant expression
pub fn make_constant(constant: &move_stackless_bytecode::stackless_bytecode::Constant) -> Expression {
    Expression::Constant(convert_constant(constant))
}

/// Create a temporary expression
pub fn make_temporary(temp: usize) -> Expression {
    Expression::Temporary(temp as TempId)
}
