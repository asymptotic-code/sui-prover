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
    let nodes = discover_region(&mut ctx, entry, exit);
    IRNode::Block { children: nodes }
}

fn discover_region(ctx: &mut DiscoveryContext, start: BlockId, stop: BlockId) -> Vec<IRNode> {
    let mut nodes = Vec::new();
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
            nodes.extend(header);

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

                nodes.push(IRNode::While {
                    cond: Box::new(cond),
                    body: Box::new(IRNode::Block {
                        children: body_nodes,
                    }),
                    vars: vec![], // Phi detection will populate this later
                    invariants: vec![],
                });

                cursor = exit_block;
                continue;
            }

            let merge =
                find_merge_block(&ctx.forward_cfg, then_block, else_block, stop).unwrap_or(stop);

            let mut then_nodes = discover_region(ctx, then_block, merge);
            let mut else_nodes = discover_region(ctx, else_block, merge);

            // Check if merge block contains only terminating code (e.g., shared return)
            // If so, include it in branches that don't already terminate
            let mut merge_included = false;
            if let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, merge) {
                let merge_nodes = ir_translator::translate_range(ctx, lower..=upper);
                let merge_block = IRNode::Block {
                    children: merge_nodes.clone(),
                };
                if merge_block.terminates() {
                    // Merge block terminates - include it in branches that don't already terminate
                    let then_term = IRNode::Block {
                        children: then_nodes.clone(),
                    }
                    .terminates();
                    let else_term = IRNode::Block {
                        children: else_nodes.clone(),
                    }
                    .terminates();
                    if !then_term {
                        then_nodes.extend(merge_nodes.clone());
                    }
                    if !else_term {
                        else_nodes.extend(merge_nodes);
                    }
                    merge_included = true;
                }
            }

            let then_branch = IRNode::Block {
                children: then_nodes,
            };
            let else_branch = IRNode::Block {
                children: else_nodes,
            };

            // If both branches terminate, don't continue after the if
            let both_terminate = then_branch.terminates() && else_branch.terminates();

            nodes.push(IRNode::If {
                cond: Box::new(IRNode::Var(cond_name)),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            });

            if both_terminate {
                break;
            }

            // If we included the merge block in the branches, skip past it
            if merge_included {
                cursor = next_block(ctx, merge, stop);
            } else {
                cursor = merge;
            }
            continue;
        }

        let block_nodes = ir_translator::translate_range(ctx, lower..=upper);
        nodes.extend(block_nodes);
        cursor = next_block(ctx, cursor, stop);
    }

    nodes
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
