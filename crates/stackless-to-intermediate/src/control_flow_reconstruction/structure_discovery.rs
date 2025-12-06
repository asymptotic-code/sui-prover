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
            let cond_name = ir_translator::temp_id(ctx, cond_temp);
            let then_block = resolve_label_block(ctx, then_label).expect("then label must resolve");
            let else_block = resolve_label_block(ctx, else_label).expect("else label must resolve");

            // Check if either branch is a back-edge (loop)
            // A branch is a back-edge if:
            // 1. It targets the start of the current region, OR
            // 2. It targets a block that dominates the current block, OR
            // 3. The branch target can reach back to the cursor (loop entry)
            let then_reaches_cursor = reaches(&ctx.forward_cfg, then_block, cursor, stop);
            let else_reaches_cursor = reaches(&ctx.forward_cfg, else_block, cursor, stop);

            let then_is_back =
                then_block == start || ctx.forward_dom.is_dominated_by(cursor, then_block) || then_reaches_cursor;
            let else_is_back =
                else_block == start || ctx.forward_dom.is_dominated_by(cursor, else_block) || else_reaches_cursor;

            if then_is_back || else_is_back {

                // Translate the header (condition computation) before the while
                let header = ir_translator::translate_range(ctx, lower..=upper);
                node = node.combine(header);

                let (body_start, exit_block) = if then_is_back {
                    (then_block, else_block)
                } else {
                    (else_block, then_block)
                };

                // Discover the loop body, which includes everything from body_start back to cursor (exclusive)
                let body_nodes = discover_region(ctx, body_start, cursor);

                let cond = if !then_is_back {
                    IRNode::UnOp {
                        op: UnOp::Not,
                        operand: Box::new(IRNode::Var(cond_name)),
                    }
                } else {
                    IRNode::Var(cond_name)
                };

                let while_node = IRNode::While {
                    cond: Box::new(cond),
                    body: Box::new(body_nodes),
                    vars: vec![], // Phi detection will populate this later
                };

                node = node.combine(while_node);

                cursor = exit_block;
                continue;
            }

            // Not a loop - regular if-then-else
            let header = ir_translator::translate_range(ctx, lower..=upper);
            node = node.combine(header);

            let merge =
                find_merge_block(ctx, then_block, else_block, stop).unwrap_or(stop);

            let then_ir = discover_region(ctx, then_block, merge);
            let else_ir = discover_region(ctx, else_block, merge);

            node = node.combine(IRNode::If {
                cond: Box::new(IRNode::Var(cond_name)),
                then_branch: Box::new(then_ir),
                else_branch: Box::new(else_ir),
            });

            // Continue at the merge
            cursor = merge;
            continue;
        }

        // Check if this block's successor will loop back to this block or start
        // If so, skip translation and let the loop discovery handle it
        let next = next_block(ctx, cursor, stop);
        if next != stop {
            if let Some((_next_lower, next_upper)) = block_bounds(&ctx.forward_cfg, next) {
                if let Bytecode::Branch(_, then_label, else_label, _) =
                    ctx.target.get_bytecode()[next_upper as usize].clone()
                {
                    let then_block = resolve_label_block(ctx, then_label).expect("then label must resolve");
                    let else_block = resolve_label_block(ctx, else_label).expect("else label must resolve");

                    // Check if next block branches back to current or start
                    let then_loops_back = then_block == cursor || then_block == start;
                    let else_loops_back = else_block == cursor || else_block == start;

                    if then_loops_back || else_loops_back {
                        // Don't translate, just move to next block which will handle the loop
                        cursor = next;
                        continue;
                    }
                }
            }
        }

        node  = node.combine(ir_translator::translate_range(ctx, lower..=upper));

        // Check if this block terminates (Ret or Abort) - if so, stop traversal
        if matches!(
            ctx.target.get_bytecode()[upper as usize],
            Bytecode::Ret(_, _) | Bytecode::Abort(_, _)
        ) {
            break;
        }

        cursor = next;
    }

    node
}


fn next_block(ctx: &DiscoveryContext, current: BlockId, stop: BlockId) -> BlockId {
    *ctx.forward_cfg.successors(current).first().unwrap_or(&stop)
}

/// Check if target is reachable from source (without going through stop)
fn reaches(
    cfg: &move_stackless_bytecode::stackless_control_flow_graph::StacklessControlFlowGraph,
    source: BlockId,
    target: BlockId,
    stop: BlockId,
) -> bool {
    let mut visited = BTreeSet::new();
    let mut worklist = vec![source];

    while let Some(block) = worklist.pop() {
        if block == stop || !visited.insert(block) {
            continue;
        }
        if block == target {
            return true;
        }
        worklist.extend(cfg.successors(block));
    }

    false
}

fn find_merge_block(
    ctx: &DiscoveryContext,
    then_block: BlockId,
    else_block: BlockId,
    stop: BlockId,
) -> Option<BlockId> {
    use move_stackless_bytecode::stackless_bytecode::Bytecode;

    // Helper to check if a block terminates (returns or aborts)
    let block_terminates = |block: BlockId| -> bool {
        if let Some((start, end)) = block_bounds(&ctx.forward_cfg, block) {
            let code = ctx.target.get_bytecode();
            for offset in start..=end {
                if let Some(bytecode) = code.get(offset as usize) {
                    if matches!(bytecode, Bytecode::Ret(_, _) | Bytecode::Abort(_, _)) {
                        return true;
                    }
                }
            }
        }
        false
    };

    let cfg = &ctx.forward_cfg;
    let mut then_reachable = BTreeSet::new();
    let mut worklist = vec![then_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !then_reachable.insert(block) {
            continue;
        }
        // Don't explore successors if this block terminates
        if !block_terminates(block) {
            worklist.extend(cfg.successors(block));
        }
    }

    let mut else_reachable = BTreeSet::new();
    let mut worklist = vec![else_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !else_reachable.insert(block) {
            continue;
        }
        // Don't explore successors if this block terminates
        if !block_terminates(block) {
            worklist.extend(cfg.successors(block));
        }
    }

    then_reachable.intersection(&else_reachable).copied().min()
}
