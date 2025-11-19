// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translates Move bytecode instructions to Expression IR
//!
//! Single responsibility: Convert individual bytecode operations to expressions.
//! Builds SSA registry as temps are encountered.

use crate::data::expressions::{Expression, BinOp, UnOp, CallConvention};
use crate::data::types::{TempId, TheoremType};
use crate::data::variables::VariableRegistry;
use crate::TheoremFunctionID;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Constant, Operation};
use move_model::model::{GlobalEnv, QualifiedId, FunId, DatatypeId};
use std::collections::BTreeMap;
use crate::data::structure::TheoremStructID;
use crate::data::expressions::ConstantValue;

pub struct ExpressionTranslator<'env> {
    env: &'env GlobalEnv,
    function_id_map: &'env BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
    struct_id_map: &'env BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
}

impl<'env> ExpressionTranslator<'env> {
    pub fn new(
        env: &'env GlobalEnv,
        function_id_map: &'env BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
        struct_id_map: &'env BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
    ) -> Self {
        Self { env, function_id_map, struct_id_map }
    }

    /// Convert a bytecode instruction to an expression
    /// Returns None for instructions that don't produce values (branches, labels, etc.)
    pub fn translate(
        &self,
        bytecode: &Bytecode,
        registry: &mut VariableRegistry,
    ) -> Option<Expression> {
        match bytecode {
            // Simple assignment
            Bytecode::Assign(_, dest, src, _) => {
                self.register_temp(*dest, registry);
                Some(Expression::Temporary(*src as TempId))
            }

            // Load constant
            Bytecode::Load(_, dest, constant) => {
                self.register_temp(*dest, registry);
                let value = self.convert_constant(constant);
                Some(Expression::Constant(value))
            }

            // Function call and operations
            Bytecode::Call(_, dests, operation, srcs, _) => {
                for &dest in dests {
                    self.register_temp(dest, registry);
                }

                match operation {
                    Operation::Function(module_id, fun_id, type_args) => {
                        let function_id = self.resolve_function_id(*module_id, *fun_id);
                        let args = srcs.iter()
                            .map(|&temp| Expression::Temporary(temp as TempId))
                            .collect();
                        let type_args_ir = type_args.iter()
                            .map(|ty| TheoremType::from_move_type(ty, self.env, self.struct_id_map))
                            .collect();

                        Some(Expression::Call {
                            function: function_id,
                            args,
                            type_args: type_args_ir,
                            convention: CallConvention::Monadic, // All functions use ProgramState monad
                        })
                    }

                    Operation::Pack(module_id, struct_id, _type_args) => {
                        let qualified_id = module_id.qualified(*struct_id);
                        let struct_id_ir = self.struct_id_map.get(&qualified_id).copied()
                            .unwrap_or_else(|| {
                                panic!("BUG: Struct {:?} not in struct_id_map", qualified_id)
                            });
                        let fields = srcs.iter()
                            .map(|&temp| Expression::Temporary(temp as TempId))
                            .collect();

                        Some(Expression::Pack {
                            struct_id: struct_id_ir,
                            fields,
                        })
                    }

                    // Unpack is handled specially in statement translator
                    // to create multiple Let statements (one per field)
                    Operation::Unpack(..) => None,

                    // Binary operations
                    Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod |
                    Operation::BitOr | Operation::BitAnd | Operation::Xor | Operation::Shl | Operation::Shr |
                    Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge | Operation::Or | Operation::And |
                    Operation::Eq | Operation::Neq => {
                        if srcs.len() != 2 {
                            panic!("BUG: Binary operation with {} operands", srcs.len());
                        }
                        let bin_op = self.convert_binop(operation);
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
                            op: UnOp::Not,
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

                    _ => None, // Other operations not yet supported
                }
            }

            // Instructions that don't produce expressions
            Bytecode::Label(_, _)
            | Bytecode::Jump(_, _)
            | Bytecode::Branch(_, _, _, _)
            | Bytecode::Ret(_, _)
            | Bytecode::Abort(_, _)
            | Bytecode::Nop(_) => None,

            _ => None, // Other bytecodes not yet implemented
        }
    }

    /// Register a temp in the SSA registry
    fn register_temp(&self, temp: usize, registry: &mut VariableRegistry) {
        let temp_id = temp as TempId;
        if registry.get_name(temp_id).is_none() {
            registry.set_name(temp_id, format!("t{}", temp));
        }
    }

    /// Convert Move constant to ConstantValue
    fn convert_constant(&self, constant: &Constant) -> ConstantValue {
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
                    .map(|elem| self.convert_constant(elem))
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
    fn convert_binop(&self, op: &Operation) -> BinOp {
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


    /// Resolve struct ID from Move module and datatype IDs
    pub fn resolve_struct_id(
        &self,
        module_id: move_model::model::ModuleId,
        struct_id: move_model::model::DatatypeId,
    ) -> TheoremStructID {
        let qualified = QualifiedId { module_id, id: struct_id };
        self.struct_id_map
            .get(&qualified)
            .copied()
            .unwrap_or_else(|| {
                let struct_env = self.env.get_module(module_id).into_struct(struct_id);
                let struct_name = struct_env.get_name().display(self.env.symbol_pool()).to_string();
                let module_name = struct_env.module_env.get_full_name_str();
                panic!("BUG: Struct {}::{} not in struct_id_map", module_name, struct_name)
            })
    }

    /// Resolve function ID from Move module and function IDs
    fn resolve_function_id(
        &self,
        module_id: move_model::model::ModuleId,
        fun_id: move_model::model::FunId,
    ) -> TheoremFunctionID {
        let qualified = QualifiedId { module_id, id: fun_id };
        self.function_id_map
            .get(&qualified)
            .copied()
            .unwrap_or_else(|| {
                let module_env = self.env.get_module(module_id);
                let func_env = module_env.get_function(fun_id);
                let func_name = func_env.get_name().display(self.env.symbol_pool()).to_string();
                panic!("BUG: Function {}::{} not found in expression translation", module_env.get_full_name_str(), func_name)
            })
    }
}
