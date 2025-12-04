// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Structure Discovery - Reconstructs structured control flow from CFG

use super::helpers::{block_bounds, resolve_label_block};
use super::DiscoveryContext;
use crate::translation::ir_translator;
use intermediate_theorem_format::{IRNode, UnOp};
use move_stackless_bytecode::stackless_bytecode::Bytecode;
use move_stackless_bytecode::stackless_control_flow_graph::BlockId;
use std::collections::BTreeSet;

pub fn reconstruct_function(mut ctx: DiscoveryContext) -> IRNode {
    let entry = ctx.forward_cfg.entry_block();
    let exit = ctx.forward_cfg.exit_block();
    discover_region(&mut ctx, entry, exit)
}

fn discover_region(ctx: &mut DiscoveryContext, start: BlockId, stop: BlockId) -> IRNode {
    let mut node = IRNode::default();
    let mut cursor = start;

    while cursor != stop {
        let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, cursor) else {
            cursor = next_block(ctx, cursor, stop);
            continue;
        };

        if let Bytecode::Branch(_, then_label, else_label, cond_temp) =
            ctx.target.get_bytecode()[upper as usize].clone()
        {
            let cond_name = ir_translator::temp_id(&ctx.target, cond_temp);
            let then_block = resolve_label_block(ctx, then_label).expect("then label must resolve");
            let else_block = resolve_label_block(ctx, else_label).expect("else label must resolve");

            let header = ir_translator::translate_range(ctx, lower..=upper);
            node = node.combine(header);

            let then_is_back =
                then_block == start || ctx.forward_dom.is_dominated_by(cursor, then_block);
            let else_is_back =
                else_block == start || ctx.forward_dom.is_dominated_by(cursor, else_block);

            if then_is_back || else_is_back {
                let (body_start, exit_block) = if then_is_back {
                    (then_block, else_block)
                } else {
                    (else_block, then_block)
                };

                let body_nodes = discover_region(ctx, body_start, cursor);

                let cond = if !then_is_back {
                    IRNode::UnOp {
                        op: UnOp::Not,
                        operand: Box::new(IRNode::Var(cond_name)),
                    }
                } else {
                    IRNode::Var(cond_name)
                };

                node = node.combine(IRNode::While {
                    cond: Box::new(cond),
                    body: Box::new(body_nodes),
                    vars: vec![], // Phi detection will populate this later
                });

                cursor = exit_block;
                continue;
            }

            let merge =
                find_merge_block(&ctx.forward_cfg, then_block, else_block, stop).unwrap_or(stop);

            node = node.combine(IRNode::If {
                cond: Box::new(IRNode::Var(cond_name)),
                then_branch: Box::new(discover_region(ctx, then_block, merge)),
                else_branch: Box::new(discover_region(ctx, else_block, merge)),
            });

            // Continue at the merge
            cursor = merge;
            continue;
        }

        node  = node.combine(ir_translator::translate_range(ctx, lower..=upper));
        cursor = next_block(ctx, cursor, stop);
    }

    node
}


fn next_block(ctx: &DiscoveryContext, current: BlockId, stop: BlockId) -> BlockId {
    *ctx.forward_cfg.successors(current).first().unwrap_or(&stop)
}

fn find_merge_block(
    cfg: &move_stackless_bytecode::stackless_control_flow_graph::StacklessControlFlowGraph,
    then_block: BlockId,
    else_block: BlockId,
    stop: BlockId,
) -> Option<BlockId> {
    let mut then_reachable = BTreeSet::new();
    let mut worklist = vec![then_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !then_reachable.insert(block) {
            continue;
        }
        worklist.extend(cfg.successors(block));
    }

    let mut else_reachable = BTreeSet::new();
    let mut worklist = vec![else_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !else_reachable.insert(block) {
            continue;
        }
        worklist.extend(cfg.successors(block));
    }

    then_reachable.intersection(&else_reachable).copied().min()
}
