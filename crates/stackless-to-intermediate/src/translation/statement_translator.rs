// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Statement translation from Move bytecode to TheoremIR statements
//!
//! Single responsibility: Convert bytecode instructions into Statement IR nodes.
//! Uses expression translator functions for expression-level operations.

use super::utilities::resolve_struct_id;
use super::expression_translator;
use crate::control_flow_reconstruction::DiscoveryContext;
use intermediate_theorem_format::VariableRegistry;
use intermediate_theorem_format::{Expression, Statement, TempId};
use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::borrow_analysis::BorrowAnnotation;
use move_stackless_bytecode::stackless_bytecode::{BorrowEdge, BorrowNode};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};
use std::ops::RangeInclusive;

pub fn translate_range(ctx: &mut DiscoveryContext, range: RangeInclusive<CodeOffset>) -> Statement {
    range
        .map(|offset| translate(ctx, offset))
        .fold(Statement::default(), Statement::combine)
}

/// Translate one bytecode to exactly one statement (or Statement::default() for Label/Nop/control flow)
pub fn translate(
    ctx: &mut DiscoveryContext,
    offset: CodeOffset,
) -> Statement {
    match &ctx.code[offset as usize] {
        // Simple assignment
        Bytecode::Assign(_, dest, src, _) => {
            register_temp(*dest, &ctx.registry);
            make_let(
                vec![*dest as TempId],
                expression_translator::make_temporary(*src),
                ctx.registry,
            )
        }

        // Load constant
        Bytecode::Load(_, dest, constant) => {
            register_temp(*dest, &ctx.registry);
            make_let(
                vec![*dest as TempId],
                expression_translator::make_constant(constant),
                ctx.registry,
            )
        }

        // Call operations - dispatch on Operation
        Bytecode::Call(_, dests, operation, srcs, _) => {
            translate_call(ctx, dests, operation, srcs, offset)
        }

        // Control flow
        Bytecode::Ret(_, temps) => {
            Statement::Return {
                values: temps.iter().map(|&t| Expression::Temporary(t as TempId)).collect(),
            }
        }

        Bytecode::Abort(_, temp) => {
            Statement::Abort {
                code: Expression::Temporary(*temp as TempId),
            }
        }

        // CFG reconstruction handles these - skip them
        Bytecode::Label(_, _)
        | Bytecode::Jump(_, _)
        | Bytecode::Branch(_, _, _, _)
        | Bytecode::Nop(_) => Statement::default(),

        _ => panic!(
            "BUG: Unsupported bytecode construct {:?} in statement translation",
            ctx.code[offset as usize]
        ),
    }
}

/// Translate Call bytecode - dispatch on Operation type
fn translate_call(
    ctx: &mut DiscoveryContext,
    dests: &[usize],
    operation: &Operation,
    srcs: &[usize],
    offset: CodeOffset,
) -> Statement {
    // Verify all destination temps are registered
    for &dest in dests {
        register_temp(dest, &ctx.registry);
    }

    match operation {
        // Unpack: destructure struct (MULTI-RESULT)
        Operation::Unpack(module_id, struct_id, _type_args) => {
            if srcs.is_empty() {
                panic!("BUG: Unpack operation with no source");
            }

            let qualified_id = module_id.qualified(*struct_id);
            let struct_id_ir = ctx.builder.get_or_reserve_struct_id(qualified_id);

            make_let(
                dests.iter().map(|&d| d as TempId).collect(),
                Expression::Unpack {
                    struct_id: struct_id_ir,
                    operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                },
                ctx.registry,
            )
        }

        Operation::UnpackVariant(module_id, struct_id, _variant_id, _type_args, _ref_type) => {
            let qualified_id = module_id.qualified(*struct_id);

            // Get or create struct ID
            let struct_id_ir = ctx.builder.get_or_reserve_struct_id(qualified_id);

            if srcs.is_empty() {
                panic!("BUG: UnpackVariant operation with no source");
            }

            make_let(
                dests.iter().map(|&d| d as TempId).collect(),
                Expression::Unpack {
                    struct_id: struct_id_ir,
                    operand: Box::new(Expression::Temporary(srcs[0] as TempId)),
                },
                ctx.registry,
            )
        }

        // WriteRef: special handling with borrow analysis
        Operation::WriteRef => {
            if srcs.len() != 2 {
                panic!("BUG: WriteRef expects 2 sources, got {}", srcs.len());
            }
            translate_write_ref(ctx, offset, srcs[0], srcs[1])
        }

        // Special handling for Prover::requires and Prover::ensures
        Operation::Function(module_id, fun_id, _type_args) => {
            let module_env = ctx.builder.env().get_module(*module_id);
            let func_env = module_env.get_function(*fun_id);
            let func_name = func_env.get_name().display(ctx.builder.env().symbol_pool()).to_string();
            let module_name = module_env.get_name().display(ctx.builder.env().symbol_pool()).to_string();

            // Handle Prover::requires and Prover::ensures specially
            // The prover module is at address 0x0 with name "prover"
            let is_prover_module = module_name == "prover" &&
                module_env.self_address() == &move_core_types::account_address::AccountAddress::ZERO;

            if is_prover_module {
                if func_name == "requires" && srcs.len() == 1 {
                    return Statement::Requires {
                        condition: Expression::Temporary(srcs[0] as TempId),
                    };
                } else if func_name == "ensures" && srcs.len() == 1 {
                    return Statement::Ensures {
                        condition: Expression::Temporary(srcs[0] as TempId),
                    };
                }
            }

            // Regular function call - use expression translator
            if let Some(expr) = expression_translator::translate_operation(&mut *ctx.builder, operation, srcs) {
                make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    expr,
                    ctx.registry,
                )
            } else {
                Statement::default()
            }
        }

        // Debug/trace operations - filter these out
        Operation::TraceLocal(_) | Operation::TraceReturn(_) |
        Operation::TraceAbort | Operation::TraceExp(_, _) |
        Operation::TraceGlobalMem(_) => Statement::default(),

        // Destroy - no statement needed
        Operation::Destroy => Statement::default(),

        // Global operations don't exist in modern Sui - all state is object-based
        Operation::GetGlobal(..) | Operation::MoveFrom(..) | Operation::MoveTo(..) |
        Operation::Exists(..) => unreachable!("Global operations don't exist in modern Sui - all state is object-based"),

        // BorrowField and BorrowLoc that return identity - need special handling
        Operation::BorrowField(..) | Operation::BorrowLoc | Operation::BorrowGlobal(..) |
        Operation::ReadRef | Operation::FreezeRef => {
            if dests.is_empty() || srcs.is_empty() {
                return Statement::default();
            }

            // Try expression translator first
            if let Some(expr) = expression_translator::translate_operation(&mut *ctx.builder, operation, srcs) {
                make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    expr,
                    ctx.registry,
                )
            } else {
                Statement::default()
            }
        }

        // All other operations: try expression translator
        _ => {
            if let Some(expr) = expression_translator::translate_operation(&mut *ctx.builder, operation, srcs) {
                make_let(
                    dests.iter().map(|&d| d as TempId).collect(),
                    expr,
                    ctx.registry,
                )
            } else {
                Statement::default()
            }
        }
    }
}

/// Translate WriteRef operation using borrow analysis
fn translate_write_ref(
    ctx: &mut DiscoveryContext,
    offset: CodeOffset,
    ref_temp: usize,
    value_temp: usize,
) -> Statement {
    // Get borrow annotation from function target
    let borrow_annotation = ctx.target.get_annotations().get::<BorrowAnnotation>();

    if borrow_annotation.is_none() {
        panic!("BUG: WriteRef requires borrow annotation but none found for function {:?}", ctx.target.get_name());
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
        if ref_temp < ctx.target.get_parameter_count() {
            let param_type = ctx.registry.get_type(ref_temp as TempId)
                .cloned()
                .unwrap();

            return Statement::Let {
                results: vec![ref_temp as TempId],
                operation: Expression::Temporary(value_temp as TempId),
                result_types: vec![param_type],
            };
        } else {
            panic!("BUG: WriteRef to reference {} with no incoming edges and not a parameter", ref_temp);
        }
    }

    let (parent_node, edge) = incoming.first().unwrap();

    match (parent_node, edge) {
        (BorrowNode::LocalRoot(local_idx), BorrowEdge::Direct) => {
            // Direct borrow: &mut x
            let local_type = ctx.registry.get_type(*local_idx as TempId)
                .cloned()
                .unwrap();

            Statement::Let {
                results: vec![*local_idx as TempId],
                operation: Expression::Temporary(value_temp as TempId),
                result_types: vec![local_type],
            }
        }

        (BorrowNode::LocalRoot(local_idx), BorrowEdge::Field(struct_qid, field_idx)) => {
            // Field borrow: &mut struct.field
            let struct_id = resolve_struct_id(&mut *ctx.builder, struct_qid.module_id, struct_qid.id);

            Statement::UpdateField {
                target: Expression::Temporary(*local_idx as TempId),
                struct_id,
                field_index: *field_idx,
                new_value: Expression::Temporary(value_temp as TempId),
            }
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
    results: Vec<TempId>,
    operation: Expression,
    registry: &VariableRegistry,
) -> Statement {
    let result_types = results.iter()
        .map(|&temp_id| {
            let base_type = registry
                .get_type(temp_id)
                .cloned()
                .unwrap();

            // If the operation is a monadic function call, wrap result type in Except
            // Pure calls (native functions) don't need wrapping
            if let Expression::Call { convention, .. } = &operation {
                if *convention == intermediate_theorem_format::CallConvention::Monadic {
                    base_type.wrap_in_monad()
                } else {
                    base_type
                }
            } else {
                base_type
            }
        })
        .collect();
    Statement::Let {
        results,
        operation,
        result_types,
    }
}

/// Ensure a temp is registered in the SSA registry
/// All bytecode temps should already be registered by populate_types
fn register_temp(temp: usize, registry: &VariableRegistry) {
    let temp_id = temp as TempId;
    // All bytecode temps should be pre-registered by populate_types
    // If not, it's a bug in the translation pipeline
    assert!(
        registry.get_name(temp_id).is_some() || registry.has_bytecode_temp(temp_id),
        "BUG: temp {} not registered - populate_types should have registered all bytecode temps",
        temp
    );
}
