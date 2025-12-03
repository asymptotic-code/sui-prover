// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified translation from Move bytecode to TheoremIR

use super::{convert_binop, convert_constant};
use crate::control_flow_reconstruction::DiscoveryContext;
use intermediate_theorem_format::{IRNode, TempId, UnOp};
use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::borrow_analysis::BorrowAnnotation;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{BorrowEdge, BorrowNode, Bytecode, Constant, Operation};
use std::ops::RangeInclusive;

pub fn translate_range(ctx: &mut DiscoveryContext, range: RangeInclusive<CodeOffset>) -> Vec<IRNode> {
    range.filter_map(|offset| translate(ctx, offset)).collect()
}

pub fn translate(ctx: &mut DiscoveryContext, offset: CodeOffset) -> Option<IRNode> {
    let bytecode = ctx.target.get_bytecode()[offset as usize].clone();
    match &bytecode {
        Bytecode::Assign(_, dest, src, _) => {
            Some(make_let(&ctx.target, &[*dest], make_var(&ctx.target, *src)))
        }

        Bytecode::Load(_, dest, constant) => {
            Some(make_let(&ctx.target, &[*dest], make_constant(constant)))
        }

        Bytecode::Call(_, dests, operation, srcs, _) => {
            translate_call(ctx, dests, operation, srcs, offset)
        }

        Bytecode::Ret(_, temps) => Some(IRNode::Return(
            temps.iter().map(|&t| make_var(&ctx.target, t)).collect(),
        )),

        Bytecode::Abort(_, temp) => {
            Some(IRNode::Abort(Box::new(make_var(&ctx.target, *temp))))
        }

        Bytecode::Label(_, _) | Bytecode::Jump(_, _) | Bytecode::Branch(_, _, _, _) | Bytecode::Nop(_) => None,

        _ => panic!("BUG: Unsupported bytecode {:?}", bytecode),
    }
}

fn translate_call(
    ctx: &mut DiscoveryContext,
    dests: &[usize],
    operation: &Operation,
    srcs: &[usize],
    offset: CodeOffset,
) -> Option<IRNode> {
    let make_let_from_expr = |expr| make_let(&ctx.target, dests, expr);

    match operation {
        Operation::Unpack(module_id, struct_id, _)
        | Operation::UnpackVariant(module_id, struct_id, _, _, _) => {
            assert!(!srcs.is_empty(), "BUG: Unpack with no source");
            let struct_id_ir = ctx.builder.struct_id(module_id.qualified(*struct_id));
            Some(make_let_from_expr(IRNode::Unpack {
                struct_id: struct_id_ir,
                value: Box::new(make_var(&ctx.target, srcs[0])),
            }))
        }
        
        Operation::Pack(module_id, struct_id, type_args)
        | Operation::PackVariant(module_id, struct_id, _, type_args) => {
            let struct_id_ir = ctx.builder.struct_id(module_id.qualified(*struct_id));
            Some(make_let_from_expr(IRNode::Pack {
                struct_id: struct_id_ir,
                type_args: type_args.iter().map(|ty| ctx.builder.convert_type(ty)).collect(),
                fields: srcs.iter().map(|&temp| make_var(&ctx.target, temp)).collect(),
            }))
        }

        Operation::Function(module_id, fun_id, type_args) => {
            let module_env = ctx.builder.env().get_module(*module_id);
            let func_env = module_env.get_function(*fun_id);
            let func_name = func_env.get_name().display(ctx.builder.env().symbol_pool()).to_string();
            let module_name = module_env.get_name().display(ctx.builder.env().symbol_pool()).to_string();

            let is_prover_module = module_name == "prover"
                && module_env.self_address() == &move_core_types::account_address::AccountAddress::ZERO;

            if is_prover_module && srcs.len() == 1 {
                if func_name == "requires" {
                    return Some(IRNode::Requires(Box::new(make_var(&ctx.target, srcs[0]))));
                } else if func_name == "ensures" {
                    return Some(IRNode::Ensures(Box::new(make_var(&ctx.target, srcs[0]))));
                }
            }
            
            Some(make_let_from_expr(IRNode::Call {
                function: ctx.builder.function_id(module_id.qualified(*fun_id)),
                args: srcs.iter().map(|&temp| make_var(&ctx.target, temp)).collect(),
                type_args: type_args.iter().map(|ty| ctx.builder.convert_type(ty)).collect(),
            }))
        }
        
        Operation::GetField(module_id, struct_id, _, field_idx)
        | Operation::BorrowField(module_id, struct_id, _, field_idx) => {
            if srcs.is_empty() {
                return None;
            }
            let struct_id_ir = ctx.builder.struct_id(module_id.qualified(*struct_id));
            Some(make_let_from_expr(IRNode::Field {
                struct_id: struct_id_ir,
                field_index: *field_idx,
                base: Box::new(make_var(&ctx.target, srcs[0])),
            }))
        }
        
        Operation::BorrowLoc | Operation::BorrowGlobal(..)
        | Operation::ReadRef | Operation::FreezeRef => {
            if dests.is_empty() || srcs.is_empty() {
                return None;
            }
            Some(make_let_from_expr(make_var(&ctx.target, srcs[0])))
        }
        
        Operation::WriteRef => {
            assert_eq!(srcs.len(), 2, "BUG: WriteRef expects 2 sources, got {}", srcs.len());
            Some(translate_write_ref(ctx, offset, srcs[0], srcs[1]))
        }
        
        Operation::Add | Operation::Sub | Operation::Mul | Operation::Div | Operation::Mod
        | Operation::BitOr | Operation::BitAnd | Operation::Xor | Operation::Shl | Operation::Shr
        | Operation::Lt | Operation::Gt | Operation::Le | Operation::Ge
        | Operation::Or | Operation::And | Operation::Eq | Operation::Neq => {
            assert_eq!(srcs.len(), 2, "BUG: Binary operation with {} operands", srcs.len());
            Some(make_let_from_expr(IRNode::BinOp {
                op: convert_binop(operation),
                lhs: Box::new(make_var(&ctx.target, srcs[0])),
                rhs: Box::new(make_var(&ctx.target, srcs[1])),
            }))
        }

        Operation::Not => {
            assert_eq!(srcs.len(), 1, "BUG: Unary operation with {} operands", srcs.len());
            Some(make_let_from_expr(IRNode::UnOp {
                op: UnOp::Not,
                operand: Box::new(make_var(&ctx.target, srcs[0])),
            }))
        }

        Operation::CastU8 | Operation::CastU16 | Operation::CastU32
        | Operation::CastU64 | Operation::CastU128 | Operation::CastU256 => {
            assert_eq!(srcs.len(), 1, "BUG: Cast operation with {} operands", srcs.len());
            let op = match operation {
                Operation::CastU8 => UnOp::CastU8,
                Operation::CastU16 => UnOp::CastU16,
                Operation::CastU32 => UnOp::CastU32,
                Operation::CastU64 => UnOp::CastU64,
                Operation::CastU128 => UnOp::CastU128,
                Operation::CastU256 => UnOp::CastU256,
                _ => unreachable!(),
            };
            Some(make_let_from_expr(IRNode::UnOp {
                op,
                operand: Box::new(make_var(&ctx.target, srcs[0])),
            }))
        }

        // Skipped debug ops
        Operation::Destroy | Operation::TraceLocal(_) | Operation::TraceReturn(_)
        | Operation::TraceAbort | Operation::TraceExp(_, _)
        | Operation::TraceGlobalMem(_) | Operation::TraceGhost(_, _) => None,
        
        Operation::GetGlobal(..) | Operation::MoveFrom(..) | Operation::MoveTo(..) | Operation::Exists(..) => {
            unreachable!("Global operations don't exist in modern Sui")
        }
        
        _ => unreachable!()
    }
}

fn translate_write_ref(
    ctx: &mut DiscoveryContext,
    offset: CodeOffset,
    ref_temp: usize,
    value_temp: usize,
) -> IRNode {
    let borrow_annotation = ctx.target.get_annotations().get::<BorrowAnnotation>();
    assert!(borrow_annotation.is_some(), "BUG: WriteRef requires borrow annotation");

    let borrow_info_at_offset = borrow_annotation.and_then(|ann| ann.get_borrow_info_at(offset));
    assert!(borrow_info_at_offset.is_some(), "BUG: No borrow info at offset {}", offset);

    let borrow_info = &borrow_info_at_offset.unwrap().before;
    let ref_node = BorrowNode::Reference(ref_temp);
    let incoming = borrow_info.get_incoming(&ref_node);

    if incoming.is_empty() {
        if ref_temp < ctx.target.get_parameter_count() {
            return make_let(&ctx.target, &[ref_temp], make_var(&ctx.target, value_temp));
        }
        panic!("BUG: WriteRef to reference {} with no incoming edges", ref_temp);
    }

    let (parent_node, edge) = incoming.first().unwrap();

    match (parent_node, edge) {
        (BorrowNode::LocalRoot(local_idx), BorrowEdge::Direct) => {
            make_let(&ctx.target, &[*local_idx], make_var(&ctx.target, value_temp))
        }

        (BorrowNode::LocalRoot(local_idx), BorrowEdge::Field(struct_qid, field_idx)) => {
            let struct_id = ctx.builder.struct_id(struct_qid.to_qualified_id());
            IRNode::UpdateField {
                base: Box::new(make_var(&ctx.target, *local_idx)),
                struct_id,
                field_index: *field_idx,
                value: Box::new(make_var(&ctx.target, value_temp)),
            }
        }

        (BorrowNode::LocalRoot(_), BorrowEdge::Index(_)) => unimplemented!("Vector element WriteRef"),
        (BorrowNode::LocalRoot(_), BorrowEdge::Hyper(_)) => unimplemented!("Nested field WriteRef"),
        (BorrowNode::LocalRoot(_), BorrowEdge::DynamicField(..)) => unimplemented!("Dynamic field WriteRef"),
        (BorrowNode::GlobalRoot(_), _) => unimplemented!("Global WriteRef"),
        _ => panic!("BUG: Unsupported WriteRef pattern: {:?}, {:?}", parent_node, edge),
    }
}

/// Convert a TempIndex to a TempId by looking up the name from the function target
pub fn temp_id(target: &FunctionTarget, temp: usize) -> TempId {
    let symbol = target.get_local_name(temp);
    target.global_env().symbol_pool().string(symbol).to_string()
}

fn make_var(target: &FunctionTarget, temp: usize) -> IRNode {
    IRNode::Var(temp_id(target, temp))
}

fn make_constant(constant: &Constant) -> IRNode {
    IRNode::Const(convert_constant(constant))
}

fn make_let(target: &FunctionTarget, results: &[usize], value: IRNode) -> IRNode {
    IRNode::Let {
        pattern: results.iter().map(|&temp| temp_id(target, temp)).collect(),
        value: Box::new(value),
    }
}