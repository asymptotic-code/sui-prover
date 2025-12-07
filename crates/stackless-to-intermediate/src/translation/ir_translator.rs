// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified translation from Move bytecode to TheoremIR

use super::{convert_binop, convert_constant};
use crate::control_flow_reconstruction::DiscoveryContext;
use intermediate_theorem_format::{IRNode, TempId, UnOp};
use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::borrow_analysis::BorrowAnnotation;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{
    BorrowEdge, BorrowNode, Bytecode, Constant, Operation,
};
use std::collections::BTreeMap;
use std::ops::RangeInclusive;

/// Build a mapping from temp indices to traced variable names by scanning TraceLocal operations
pub fn build_trace_map(target: &FunctionTarget) -> BTreeMap<usize, String> {
    let mut trace_map = BTreeMap::new();

    // Get the number of parameters - these are local variables 0..num_params-1
    let num_params = target.get_parameter_count();

    for bytecode in target.get_bytecode() {
        if let Bytecode::Call(_, _, Operation::TraceLocal(local_idx), srcs, _) = bytecode {
            // TraceLocal(local_idx) traces the value in srcs[0] to the variable at local_idx
            if !srcs.is_empty() {
                let source_temp = srcs[0];

                // Only map temps that are NOT parameters
                // Parameters (temps 0..num_params-1) should keep their original names
                if source_temp >= num_params {
                    let symbol = target.get_local_name(*local_idx);
                    let traced_name = target.global_env().symbol_pool().string(symbol).to_string();

                    // Strip version suffixes from traced name
                    let traced_name = if let Some(hash_pos) = traced_name.find('#') {
                        traced_name[..hash_pos].to_string()
                    } else {
                        traced_name
                    };

                    trace_map.insert(source_temp, traced_name);
                }
            }
        }
    }

    trace_map
}

pub fn translate_range(
    ctx: &mut DiscoveryContext,
    range: RangeInclusive<CodeOffset>,
) -> IRNode {
    let mut result = IRNode::default();
    for offset in range {
        let node = translate(ctx, offset);
        let terminates = node.terminates();
        result = result.combine(node);
        // Stop translating if we hit a terminating instruction
        if terminates {
            break;
        }
    }
    result
}

pub fn translate(ctx: &mut DiscoveryContext, offset: CodeOffset) -> IRNode {
    let bytecode = ctx.target.get_bytecode()[offset as usize].clone();

    match &bytecode {
        Bytecode::Assign(_, dest, src, _) => {
            make_let(ctx, &[*dest], make_var(ctx, *src))
        }

        Bytecode::Load(_, dest, constant) => {
            let dest_type = ctx.builder.convert_type(ctx.target.get_local_type(*dest));
            make_let(ctx, &[*dest], make_constant(constant, &dest_type))
        }

        Bytecode::Call(_, dests, operation, srcs, _) => {
            translate_call(ctx, dests, operation, srcs, offset)
        }

        Bytecode::Ret(_, temps) => IRNode::Return(
            temps.iter().map(|&t| make_var(ctx, t)).collect(),
        ),

        Bytecode::Abort(_, temp) => IRNode::Abort(Box::new(make_var(ctx, *temp))),

        Bytecode::Label(_, _)
        | Bytecode::Jump(_, _)
        | Bytecode::Branch(_, _, _, _)
        | Bytecode::Nop(_) => IRNode::default(),

        _ => panic!("BUG: Unsupported bytecode {:?}", bytecode),
    }
}

fn translate_call(
    ctx: &mut DiscoveryContext,
    dests: &[usize],
    operation: &Operation,
    srcs: &[usize],
    offset: CodeOffset,
) -> IRNode {
    match operation {
        Operation::Unpack(module_id, struct_id, _)
        | Operation::UnpackVariant(module_id, struct_id, _, _, _) => {
            assert!(!srcs.is_empty(), "BUG: Unpack with no source");
            let struct_id_ir = ctx.builder.struct_id(module_id.qualified(*struct_id));
            make_let(ctx, dests, IRNode::Unpack {
                struct_id: struct_id_ir,
                value: Box::new(make_var(ctx, srcs[0])),
            })
        }

        Operation::Pack(module_id, struct_id, type_args)
        | Operation::PackVariant(module_id, struct_id, _, type_args) => {
            let struct_id_ir = ctx.builder.struct_id(module_id.qualified(*struct_id));
            let type_args = type_args
                .iter()
                .map(|ty| ctx.builder.convert_type(ty))
                .collect();
            let fields = srcs
                .iter()
                .map(|&temp| make_var(ctx, temp))
                .collect();
            make_let(ctx, dests, IRNode::Pack {
                struct_id: struct_id_ir,
                type_args,
                fields,
            })
        }

        Operation::Function(module_id, fun_id, type_args) => {
            let module_env = ctx.builder.env().get_module(*module_id);
            let func_env = module_env.get_function(*fun_id);
            let func_name = func_env
                .get_name()
                .display(ctx.builder.env().symbol_pool())
                .to_string();
            let module_name = module_env
                .get_name()
                .display(ctx.builder.env().symbol_pool())
                .to_string();

            let is_prover_module =
                module_name == "prover" && module_env.self_address().iter().all(|val| *val == 0);

            if is_prover_module && srcs.len() == 1 {
                if func_name == "requires" {
                    return IRNode::Requires(Box::new(make_var(ctx, srcs[0])));
                } else if func_name == "ensures" {
                    return IRNode::Ensures(Box::new(make_var(ctx, srcs[0])));
                }
            }

            let function = ctx.builder.function_id(module_id.qualified(*fun_id));
            let args = srcs
                .iter()
                .map(|&temp| make_var(ctx, temp))
                .collect();
            let type_args = type_args
                .iter()
                .map(|ty| ctx.builder.convert_type(ty))
                .collect();
            make_let(ctx, dests, IRNode::Call {
                function,
                args,
                type_args,
            })
        }

        Operation::GetField(module_id, struct_id, _, field_idx)
        | Operation::BorrowField(module_id, struct_id, _, field_idx) => {
            if srcs.is_empty() {
                return IRNode::default();
            }
            let struct_id_ir = ctx.builder.struct_id(module_id.qualified(*struct_id));
            make_let(ctx, dests, IRNode::Field {
                struct_id: struct_id_ir,
                field_index: *field_idx,
                base: Box::new(make_var(ctx, srcs[0])),
            })
        }

        Operation::BorrowLoc
        | Operation::BorrowGlobal(..)
        | Operation::ReadRef
        | Operation::FreezeRef => {
            if dests.is_empty() || srcs.is_empty() {
                return IRNode::default();
            }
            make_let(ctx, dests, make_var(ctx, srcs[0]))
        }

        Operation::WriteRef => {
            assert_eq!(
                srcs.len(),
                2,
                "BUG: WriteRef expects 2 sources, got {}",
                srcs.len()
            );
            translate_write_ref(ctx, offset, srcs[0], srcs[1])
        }

        Operation::Add
        | Operation::Sub
        | Operation::Mul
        | Operation::Div
        | Operation::Mod
        | Operation::BitOr
        | Operation::BitAnd
        | Operation::Xor
        | Operation::Shl
        | Operation::Shr
        | Operation::Lt
        | Operation::Gt
        | Operation::Le
        | Operation::Ge
        | Operation::Or
        | Operation::And
        | Operation::Eq
        | Operation::Neq => {
            assert_eq!(
                srcs.len(),
                2,
                "BUG: Binary operation with {} operands",
                srcs.len()
            );
            make_let(ctx, dests, IRNode::BinOp {
                op: convert_binop(operation),
                lhs: Box::new(make_var(ctx, srcs[0])),
                rhs: Box::new(make_var(ctx, srcs[1])),
            })
        }

        Operation::Not => {
            assert_eq!(
                srcs.len(),
                1,
                "BUG: Unary operation with {} operands",
                srcs.len()
            );
            make_let(ctx, dests, IRNode::UnOp {
                op: UnOp::Not,
                operand: Box::new(make_var(ctx, srcs[0])),
            })
        }

        Operation::CastU8
        | Operation::CastU16
        | Operation::CastU32
        | Operation::CastU64
        | Operation::CastU128
        | Operation::CastU256 => {
            assert_eq!(
                srcs.len(),
                1,
                "BUG: Cast operation with {} operands",
                srcs.len()
            );
            let op = match operation {
                Operation::CastU8 => UnOp::CastU8,
                Operation::CastU16 => UnOp::CastU16,
                Operation::CastU32 => UnOp::CastU32,
                Operation::CastU64 => UnOp::CastU64,
                Operation::CastU128 => UnOp::CastU128,
                Operation::CastU256 => UnOp::CastU256,
                _ => unreachable!(),
            };
            make_let(ctx, dests, IRNode::UnOp {
                op,
                operand: Box::new(make_var(ctx, srcs[0])),
            })
        }

        // Skipped debug ops
        Operation::Destroy
        | Operation::TraceLocal(_)
        | Operation::TraceReturn(_)
        | Operation::TraceAbort
        | Operation::TraceExp(_, _)
        | Operation::TraceGlobalMem(_)
        | Operation::TraceGhost(_, _) => IRNode::default(),

        Operation::GetGlobal(..)
        | Operation::MoveFrom(..)
        | Operation::MoveTo(..)
        | Operation::Exists(..) => {
            unreachable!("Global operations don't exist in modern Sui")
        }

        _ => unreachable!(),
    }
}

fn translate_write_ref(
    ctx: &mut DiscoveryContext,
    offset: CodeOffset,
    ref_temp: usize,
    value_temp: usize,
) -> IRNode {
    let borrow_annotation = ctx.target.get_annotations().get::<BorrowAnnotation>();
    assert!(
        borrow_annotation.is_some(),
        "BUG: WriteRef requires borrow annotation"
    );

    let borrow_info_at_offset = borrow_annotation.and_then(|ann| ann.get_borrow_info_at(offset));
    assert!(
        borrow_info_at_offset.is_some(),
        "BUG: No borrow info at offset {}",
        offset
    );

    let borrow_info = &borrow_info_at_offset.unwrap().before;
    let ref_node = BorrowNode::Reference(ref_temp);
    let incoming = borrow_info.get_incoming(&ref_node);

    if incoming.is_empty() {
        if ref_temp < ctx.target.get_parameter_count() {
            return make_let(ctx, &[ref_temp], make_var(ctx, value_temp));
        }
        panic!(
            "BUG: WriteRef to reference {} with no incoming edges",
            ref_temp
        );
    }

    let (parent_node, edge) = incoming.first().unwrap();

    match (parent_node, edge) {
        (BorrowNode::LocalRoot(local_idx), BorrowEdge::Direct) => make_let(
            ctx,
            &[*local_idx],
            make_var(ctx, value_temp),
        ),

        (BorrowNode::LocalRoot(local_idx), BorrowEdge::Field(struct_qid, field_idx)) => {
            let struct_id = ctx.builder.struct_id(struct_qid.to_qualified_id());
            IRNode::UpdateField {
                base: Box::new(make_var(ctx, *local_idx)),
                struct_id,
                field_index: *field_idx,
                value: Box::new(make_var(ctx, value_temp)),
            }
        }

        (BorrowNode::LocalRoot(_), BorrowEdge::Index(_)) => {
            unimplemented!("Vector element WriteRef")
        }
        (BorrowNode::LocalRoot(_), BorrowEdge::Hyper(_)) => unimplemented!("Nested field WriteRef"),
        (BorrowNode::LocalRoot(_), BorrowEdge::DynamicField(..)) => {
            unimplemented!("Dynamic field WriteRef")
        }
        (BorrowNode::GlobalRoot(_), _) => unimplemented!("Global WriteRef"),
        _ => panic!(
            "BUG: Unsupported WriteRef pattern: {:?}, {:?}",
            parent_node, edge
        ),
    }
}

/// Convert a TempIndex to a TempId by looking up the name from the function target
pub fn temp_id(ctx: &DiscoveryContext, temp: usize) -> TempId {
    // First check if we have a traced name for this temp
    if let Some(traced_name) = ctx.trace_names.get(&temp) {
        return traced_name.clone();
    }

    // Otherwise fall back to the regular local name
    let symbol = ctx.target.get_local_name(temp);
    let mut name = ctx.target.global_env().symbol_pool().string(symbol).to_string();

    // Strip Move compiler's version suffixes (e.g., "sum#1#0" → "sum", "tmp#$2" → "tmp")
    if let Some(hash_pos) = name.find('#') {
        name.truncate(hash_pos);
    }

    name
}

fn make_var(ctx: &DiscoveryContext, temp: usize) -> IRNode {
    IRNode::Var(temp_id(ctx, temp))
}

fn make_constant(constant: &Constant, expected_type: &intermediate_theorem_format::Type) -> IRNode {
    IRNode::Const(convert_constant(constant, expected_type))
}

fn make_let(ctx: &DiscoveryContext, results: &[usize], value: IRNode) -> IRNode {
    IRNode::Let {
        pattern: results.iter().map(|&temp| temp_id(ctx, temp)).collect(),
        value: Box::new(value),
    }
}
