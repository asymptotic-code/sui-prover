// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Centralized bytecode translation to TheoremIR statements
//!
//! Single responsibility: Translate Move bytecode instructions to Statement IR.
//! ONE bytecode → ONE statement (or skip for Label/Nop).
//! All bytecode handling in ONE place - no splitting across files.

use crate::data::expressions::{Expression, BinOp, UnOp, CallConvention, ConstantValue};
use crate::data::statements::Statement;
use crate::data::types::{TempId, TheoremType};
use crate::data::variables::VariableRegistry;
use crate::data::structure::TheoremStructID;
use crate::TheoremFunctionID;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Constant, Operation};
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::borrow_analysis::BorrowAnnotation;
use move_stackless_bytecode::stackless_bytecode::{BorrowNode, BorrowEdge};
use move_model::model::{GlobalEnv, QualifiedId, FunId, DatatypeId};
use move_binary_format::file_format::CodeOffset;
use std::collections::BTreeMap;

pub struct BytecodeTranslator<'env, 'a> {
    env: &'env GlobalEnv,
    function_id_map: &'a BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
    struct_id_map: &'a BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
    target: &'a FunctionTarget<'a>,
}

impl<'env, 'a> BytecodeTranslator<'env, 'a> {
    pub fn new(
        env: &'env GlobalEnv,
        function_id_map: &'a BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
        struct_id_map: &'a BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
        target: &'a FunctionTarget<'a>,
    ) -> Self {
        Self {
            env,
            function_id_map,
            struct_id_map,
            target,
        }
    }

    /// Translate one bytecode to exactly one statement (or None for Label/Nop)
    pub fn translate(
        &self,
        bytecode: &Bytecode,
        offset: CodeOffset,
        registry: &mut VariableRegistry,
    ) -> Option<Statement> {
        match bytecode {
            // Simple assignment
            Bytecode::Assign(_, dest, src, _) => {
                self.register_temp(*dest, registry);
                Some(self.make_let(
                    vec![*dest as TempId],
                    Expression::Temporary(*src as TempId),
                    registry,
                ))
            }

            // Load constant
            Bytecode::Load(_, dest, constant) => {
                self.register_temp(*dest, registry);
                let value = self.convert_constant(constant);
                Some(self.make_let(
                    vec![*dest as TempId],
                    Expression::Constant(value),
                    registry,
                ))
            }

            // Call operations - dispatch on Operation
            Bytecode::Call(_, dests, operation, srcs, _) => {
                self.translate_call(dests, operation, srcs, offset, registry)
            }

            // Control flow
            Bytecode::Ret(_, temps) => {
                Some(Statement::Return {
                    values: temps.iter().map(|&t| Expression::Temporary(t as TempId)).collect(),
                })
            }

            Bytecode::Abort(_, temp) => {
                Some(Statement::Abort {
                    code: Expression::Temporary(*temp as TempId),
                })
            }

            // CFG reconstruction handles these - skip them
            Bytecode::Label(_, _)
            | Bytecode::Jump(_, _)
            | Bytecode::Branch(_, _, _, _)
            | Bytecode::Nop(_) => None,

            // Other bytecodes not yet implemented
            _ => panic!(
                "BUG: Unsupported bytecode construct {:?} in bytecode translation",
                bytecode
            ),
        }
    }

    /// Translate Call bytecode - dispatch on Operation type
    /// Returns None for operations that should be skipped (like BorrowLoc)
    fn translate_call(
        &self,
        dests: &[usize],
        operation: &Operation,
        srcs: &[usize],
        offset: CodeOffset,
        registry: &mut VariableRegistry,
    ) -> Option<Statement> {
        // Register all destination temps
        for &dest in dests {
            self.register_temp(dest, registry);
        }

        match operation {
            // Pack: create struct (single result)
            Operation::Pack(module_id, struct_id, _type_args) => {
                let qualified_id = module_id.qualified(*struct_id);
                let struct_id_ir = self.struct_id_map.get(&qualified_id).copied()
                    .unwrap_or_else(|| {
                        panic!("BUG: Struct {:?} not in struct_id_map", qualified_id)
                    });

                let fields = srcs.iter()
                    .map(|&temp| Expression::Temporary(temp as TempId))
                    .collect();

                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::Pack {
                        struct_id: struct_id_ir,
                        fields,
                    },
                    registry,
                ))
            }

            // Unpack: destructure struct (MULTI-RESULT)
            Operation::Unpack(module_id, struct_id, _type_args) => {
                if srcs.is_empty() {
                    panic!("BUG: Unpack operation with no source");
                }

                let qualified_id = module_id.qualified(*struct_id);
                let struct_id_ir = self.struct_id_map.get(&qualified_id).copied()
                    .unwrap_or_else(|| {
                        panic!("BUG: Struct {:?} not in struct_id_map", qualified_id)
                    });

                // Multi-result: use UnpackAll expression
                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::UnpackAll {
                        struct_id: struct_id_ir,
                        operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                    },
                    registry,
                ))
            }

            // WriteRef: special handling with borrow analysis
            Operation::WriteRef => {
                if srcs.len() != 2 {
                    panic!("BUG: WriteRef expects 2 sources, got {}", srcs.len());
                }
                self.translate_write_ref(offset, srcs[0], srcs[1], registry)
            }

            // Binary operations
            Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod |
            Operation::BitOr | Operation::BitAnd | Operation::Xor | Operation::Shl | Operation::Shr |
            Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge | Operation::Or | Operation::And |
            Operation::Eq | Operation::Neq => {
                if srcs.len() != 2 {
                    panic!("BUG: Binary operation with {} operands", srcs.len());
                }
                let bin_op = self.convert_binop(operation);
                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::BinOp {
                        op: bin_op,
                        lhs: Box::new(Expression::Temporary(srcs[0] as TempId)),
                        rhs: Box::new(Expression::Temporary(srcs[1] as TempId)),
                    },
                    registry,
                ))
            }

            // Unary operations
            Operation::Not => {
                if srcs.len() != 1 {
                    panic!("BUG: Unary operation with {} operands", srcs.len());
                }
                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::UnOp {
                        op: UnOp::Not,
                        operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                    },
                    registry,
                ))
            }

            // Debug/trace operations - filter these out
            Operation::TraceLocal(_) | Operation::TraceReturn(_) |
            Operation::TraceAbort | Operation::TraceExp(_, _) |
            Operation::TraceGlobalMem(_) => {
                // These are debug instrumentation - skip them
                None
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
                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::Cast {
                        value: Box::new(Expression::Temporary(srcs[0] as TempId)),
                        target_type,
                    },
                    registry,
                ))
            }

            // PackVariant and UnpackVariant - treat like Pack/Unpack for now
            // Variants are Move enums, but we can model them as tagged structs
            // Skip if struct is not resolved (happens for compiler-internal types)
            Operation::PackVariant(module_id, struct_id, _variant_id, _type_args) => {
                let qualified_id = module_id.qualified(*struct_id);

                // Skip if struct not in map (unresolved/internal type)
                if let Some(struct_id_ir) = self.struct_id_map.get(&qualified_id).copied() {
                    let fields = srcs.iter()
                        .map(|&temp| Expression::Temporary(temp as TempId))
                        .collect();

                    Some(self.make_let(
                        dests.iter().map(|&d| d as TempId).collect(),
                        Expression::Pack {
                            struct_id: struct_id_ir,
                            fields,
                        },
                        registry,
                    ))
                } else {
                    // Struct not resolved - skip this operation
                    None
                }
            }

            Operation::UnpackVariant(module_id, struct_id, _variant_id, _type_args, _ref_type) => {
                let qualified_id = module_id.qualified(*struct_id);

                // Skip if struct not in map (unresolved/internal type)
                if let Some(struct_id_ir) = self.struct_id_map.get(&qualified_id).copied() {
                    if srcs.is_empty() {
                        panic!("BUG: UnpackVariant operation with no source");
                    }

                    // Multi-result: use UnpackAll expression
                    Some(self.make_let(
                        dests.iter().map(|&d| d as TempId).collect(),
                        Expression::UnpackAll {
                            struct_id: struct_id_ir,
                            operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                        },
                        registry,
                    ))
                } else {
                    // Struct not resolved - skip this operation
                    None
                }
            }

            // GetField: extract field value from struct
            Operation::GetField(module_id, struct_id, _type_args, field_idx) => {
                if srcs.is_empty() {
                    panic!("BUG: GetField operation with no source");
                }

                let qualified_id = module_id.qualified(*struct_id);
                let struct_id_ir = self.struct_id_map.get(&qualified_id).copied()
                    .unwrap_or_else(|| {
                        panic!("BUG: Struct {:?} not in struct_id_map", qualified_id)
                    });

                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::Unpack {
                        struct_id: struct_id_ir,
                        field_index: *field_idx,
                        operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                    },
                    registry,
                ))
            }

            // BorrowField - extract field from struct
            Operation::BorrowField(module_id, struct_id, _type_args, field_index) => {
                if dests.is_empty() || srcs.is_empty() {
                    return None;
                }

                let qualified_id = module_id.qualified(*struct_id);

                // Check if struct is in the map
                if let Some(struct_id_ir) = self.struct_id_map.get(&qualified_id).copied() {
                    // Generate Unpack expression to extract the field
                    Some(self.make_let(
                        dests.iter().map(|&d| d as TempId).collect(),
                        Expression::Unpack {
                            struct_id: struct_id_ir,
                            field_index: *field_index,
                            operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                        },
                        registry,
                    ))
                } else {
                    // Struct not in map, fall back to identity assignment
                    let result_types: Vec<TheoremType> = dests.iter()
                        .map(|&dest| registry.get_type(dest as TempId)
                            .cloned()
                            .unwrap_or(TheoremType::UInt(64)))
                        .collect();

                    Some(Statement::Let {
                        results: dests.iter().map(|&d| d as TempId).collect(),
                        operation: Expression::Temporary(srcs[0] as TempId),
                        result_types,
                    })
                }
            }

            // BorrowLoc and BorrowGlobal - create identity assignments
            // In Lean, references don't exist, so borrowing just creates an alias
            Operation::BorrowLoc | Operation::BorrowGlobal(..) => {
                if dests.is_empty() || srcs.is_empty() {
                    return None;
                }
                // Get the type of the destination variable
                let result_types: Vec<TheoremType> = dests.iter()
                    .map(|&dest| registry.get_type(dest as TempId)
                        .cloned()
                        .unwrap_or(TheoremType::UInt(64))) // Default fallback
                    .collect();

                // Create identity assignment: dest = src
                Some(Statement::Let {
                    results: dests.iter().map(|&d| d as TempId).collect(),
                    operation: Expression::Temporary(srcs[0] as TempId),
                    result_types,
                })
            }

            // ReadRef - dereference in SSA just copies the value
            Operation::ReadRef => {
                if dests.is_empty() || srcs.is_empty() {
                    return None;
                }
                // Get the type of the destination variable
                let result_types: Vec<TheoremType> = dests.iter()
                    .map(|&dest| registry.get_type(dest as TempId)
                        .cloned()
                        .unwrap_or(TheoremType::UInt(64))) // Default fallback
                    .collect();

                // Create identity assignment: dest = src (dereferencing is implicit)
                Some(Statement::Let {
                    results: dests.iter().map(|&d| d as TempId).collect(),
                    operation: Expression::Temporary(srcs[0] as TempId),
                    result_types,
                })
            }

            // FreezeRef - convert mutable reference to immutable (identity assignment in Lean)
            Operation::FreezeRef => {
                if dests.is_empty() || srcs.is_empty() {
                    return None;
                }
                // Get the type of the destination variable
                let result_types: Vec<TheoremType> = dests.iter()
                    .map(|&dest| registry.get_type(dest as TempId)
                        .cloned()
                        .unwrap_or(TheoremType::UInt(64))) // Default fallback
                    .collect();

                // Create identity assignment: dest = src (freeze is a no-op in value semantics)
                Some(Statement::Let {
                    results: dests.iter().map(|&d| d as TempId).collect(),
                    operation: Expression::Temporary(srcs[0] as TempId),
                    result_types,
                })
            }

            // Destroy - these don't produce values, truly skip
            Operation::Destroy => {
                return None;
            }

            // Global operations skipped for pure functions
            Operation::GetGlobal(..) | Operation::MoveFrom(..) | Operation::MoveTo(..) |
            Operation::Exists(..) => {
                return None;
            }

            // Function calls
            Operation::Function(module_id, fun_id, type_args) => {
                let function_id = self.resolve_function_id(*module_id, *fun_id);

                // Check if this is a Prover module call (requires/ensures)
                let module_env = self.env.get_module(*module_id);
                let func_env = module_env.get_function(*fun_id);
                let func_name = func_env.get_name().display(self.env.symbol_pool()).to_string();
                let module_name = module_env.get_full_name_str();

                // Handle Prover::requires and Prover::ensures specially
                if module_name.ends_with("::prover") || module_name.ends_with("::Prover") {
                    if func_name == "requires" && srcs.len() == 1 {
                        // Translate to Requires statement
                        return Some(Statement::Requires {
                            condition: Expression::Temporary(srcs[0] as TempId),
                        });
                    } else if func_name == "ensures" && srcs.len() == 1 {
                        // Translate to Ensures statement
                        return Some(Statement::Ensures {
                            condition: Expression::Temporary(srcs[0] as TempId),
                        });
                    }
                }

                // Regular function call
                let args = srcs.iter()
                    .map(|&temp| Expression::Temporary(temp as TempId))
                    .collect();
                let type_args_ir = type_args.iter()
                    .map(|ty| TheoremType::from_move_type(ty, self.env, self.struct_id_map))
                    .collect();

                Some(self.make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    Expression::Call {
                        function: function_id,
                        args,
                        type_args: type_args_ir,
                        convention: CallConvention::Monadic, // All functions use ProgramState monad
                    },
                    registry,
                ))
            }

            _ => panic!("BUG: Unsupported operation construct {:?} in operation translation", operation),
        }
    }

    /// Translate WriteRef operation using borrow analysis
    fn translate_write_ref(
        &self,
        offset: CodeOffset,
        ref_temp: usize,
        value_temp: usize,
        registry: &VariableRegistry,
    ) -> Option<Statement> {
        // Get borrow annotation from function target
        let borrow_annotation = self.target.get_annotations().get::<BorrowAnnotation>();

        if borrow_annotation.is_none() {
            // No borrow annotation - fall back to simple assignment
            let local_type = registry.get_type(ref_temp as TempId)
                .cloned()
                .unwrap_or(TheoremType::Bool);

            return Some(Statement::Let {
                results: vec![ref_temp as TempId],
                operation: Expression::Temporary(value_temp as TempId),
                result_types: vec![local_type],
            });
        }

        let borrow_info_at_offset = borrow_annotation
            .and_then(|ann| ann.get_borrow_info_at(offset));

        if borrow_info_at_offset.is_none() {
            panic!("BUG: No borrow info at offset {} for WriteRef", offset);
        }

        let borrow_info = &borrow_info_at_offset.unwrap().before;

        // Find what this reference borrows from
        let ref_node = BorrowNode::Reference(ref_temp);
        let incoming = borrow_info.get_incoming(&ref_node);

        if incoming.is_empty() {
            // Reference parameter: function should return updated value
            if ref_temp < self.target.get_parameter_count() {
                let param_type = registry.get_type(ref_temp as TempId)
                    .cloned()
                    .unwrap_or(TheoremType::Bool);

                return Some(Statement::Let {
                    results: vec![ref_temp as TempId],
                    operation: Expression::Temporary(value_temp as TempId),
                    result_types: vec![param_type],
                });
            } else {
                panic!("BUG: WriteRef to reference {} with no incoming edges and not a parameter", ref_temp);
            }
        }

        let (parent_node, edge) = incoming.first().unwrap();

        match (parent_node, edge) {
            (BorrowNode::LocalRoot(local_idx), BorrowEdge::Direct) => {
                // Direct borrow: &mut x
                let local_type = registry.get_type(*local_idx as TempId)
                    .cloned()
                    .unwrap_or(TheoremType::Bool);

                Some(Statement::Let {
                    results: vec![*local_idx as TempId],
                    operation: Expression::Temporary(value_temp as TempId),
                    result_types: vec![local_type],
                })
            }

            (BorrowNode::LocalRoot(local_idx), BorrowEdge::Field(struct_qid, field_idx)) => {
                // Field borrow: &mut struct.field
                let struct_id = self.resolve_struct_id(struct_qid.module_id, struct_qid.id);

                Some(Statement::UpdateField {
                    target: Expression::Temporary(*local_idx as TempId),
                    struct_id,
                    field_index: *field_idx,
                    new_value: Expression::Temporary(value_temp as TempId),
                })
            }

            (BorrowNode::LocalRoot(_local_idx), BorrowEdge::Index(_index_kind)) => {
                unimplemented!("Vector element WriteRef not yet implemented - need to track index temp from BorrowLoc")
            }

            (BorrowNode::LocalRoot(_local_idx), BorrowEdge::Hyper(_edges)) => {
                unimplemented!("Nested field WriteRef (Hyper edge) not yet implemented")
            }

            (BorrowNode::LocalRoot(_local_idx), BorrowEdge::DynamicField(..)) => {
                unimplemented!("Dynamic field WriteRef not yet implemented - requires explicit map model")
            }

            (BorrowNode::GlobalRoot(_), _) => {
                unimplemented!("Global WriteRef not yet implemented - requires explicit memory model")
            }

            _ => panic!("BUG: Unsupported WriteRef pattern: parent={:?}, edge={:?}", parent_node, edge),
        }
    }

    /// Helper: create Let statement with proper types
    fn make_let(
        &self,
        results: Vec<TempId>,
        operation: Expression,
        registry: &VariableRegistry,
    ) -> Statement {
        let result_types = results.iter()
            .map(|&temp_id| {
                registry
                    .get_type(temp_id)
                    .cloned()
                    .unwrap_or(TheoremType::Bool)
            })
            .collect();
        Statement::Let {
            results,
            operation,
            result_types,
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
    fn resolve_struct_id(
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
                panic!("BUG: Function {}::{} not found in bytecode translation", module_env.get_full_name_str(), func_name)
            })
    }
}
