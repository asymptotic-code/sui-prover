// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0
use crate::stackless_bytecode::{Bytecode, Label, Operation};
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use move_binary_format::file_format::CodeOffset;
use std::collections::BTreeMap;

use super::types::StructuredBlock;

/// The context for control flow reconstruction
struct ReconstructionContext<'ctx> {
    code: &'ctx [Bytecode],
    forward_cfg: StacklessControlFlowGraph,
    back_cfg: StacklessControlFlowGraph,
    label_offsets: BTreeMap<Label, CodeOffset>,
}

impl<'ctx> ReconstructionContext<'ctx> {
    fn new(code: &'ctx [Bytecode]) -> Self {
        Self {
            code,
            forward_cfg: StacklessControlFlowGraph::new_forward_with_options(code, true),
            back_cfg: StacklessControlFlowGraph::new_backward_with_options(code, false, true),
            label_offsets: Bytecode::label_offsets(code),
        }
    }

    fn block_bounds(&self, block: BlockId) -> Option<(CodeOffset, CodeOffset)> {
        match self.forward_cfg.content(block) {
            BlockContent::Basic { lower, upper } => Some((*lower, *upper)),
            BlockContent::Dummy => None,
        }
    }
}

/// Reconstructs control flow from basic blocks into a structured representation.
pub fn reconstruct_control_flow(code: &[Bytecode]) -> Option<StructuredBlock> {
    if code
        .iter()
        .any(|bc| matches!(bc, Bytecode::Call(_, _, Operation::Stop, _, _)))
    {
        return None;
    }

    let ctx = ReconstructionContext::new(code);
    if ctx.forward_cfg.is_acyclic() {
        Some(reconstruct_region(&ctx, ctx.forward_cfg.entry_block(), None).unwrap())
    } else {
        return None;
    }
}

/// Recursively reconstructs a region into `StructuredBlock`s.
///
/// Starts at `start_block` and follows fallthrough edges until reaching `stop_block`,
/// a back-edge, or no further successors.
fn reconstruct_region(
    ctx: &ReconstructionContext,
    start_block: BlockId,
    stop_block: Option<BlockId>,
) -> Option<StructuredBlock> {
    let mut current_block = start_block;
    let mut blocks: Vec<StructuredBlock> = Vec::new();
    while Some(current_block) != stop_block {
        if let Some((lower, upper)) = ctx.block_bounds(current_block) {
            blocks.push(StructuredBlock::Basic { lower, upper });
        };
        let terminator = ctx
            .block_bounds(current_block)
            .and_then(|(_, upper)| ctx.code.get(upper as usize));
        // Structured arms are resolved by label (CFG successor order is not
        // part of its API); `VariantSwitch` and `Branch` follow the same
        // convention.
        let arm_block = |label| {
            ctx.forward_cfg
                .pc_to_block(ctx.label_offsets[label])
                .expect("branch label points at a known block")
        };
        match (
            terminator,
            ctx.forward_cfg.successors(current_block).as_slice(),
        ) {
            (Some(Bytecode::VariantSwitch(_, _, labels)), _) => {
                let switch_at = ctx.block_bounds(current_block).unwrap().1;
                let immediate_post_dominator = ctx
                    .back_cfg
                    .find_immediate_dominator(current_block)
                    .unwrap_or_else(|| {
                        ctx.forward_cfg.display();
                        ctx.back_cfg.display();
                        panic!(
                            "no post-dominator found for VariantSwitch block={}",
                            current_block
                        );
                    });
                let branches: Vec<StructuredBlock> = labels
                    .iter()
                    .map(|label| {
                        reconstruct_region(ctx, arm_block(label), Some(immediate_post_dominator))
                            .unwrap_or_else(|| StructuredBlock::Seq(Vec::new()))
                    })
                    .collect();
                blocks.push(StructuredBlock::VariantSwitch {
                    switch_at,
                    branches,
                });
                current_block = immediate_post_dominator;
            }
            (Some(Bytecode::Branch(_, then_label, else_label, _)), _) => {
                let then_block = arm_block(then_label);
                if then_label == else_label {
                    // Degenerate 2-way: `if (cond) {}` or `if (cond) {} else {}`.
                    current_block = then_block;
                    continue;
                }
                let else_block = arm_block(else_label);
                let immediate_post_dominator = ctx
                    .back_cfg
                    .find_immediate_dominator(current_block)
                    .unwrap_or_else(|| {
                        ctx.forward_cfg.display();
                        ctx.back_cfg.display();
                        panic!("no post-dominator found for block={}", current_block);
                    });
                let then_region =
                    reconstruct_region(ctx, then_block, Some(immediate_post_dominator))
                        .unwrap_or_else(|| {
                            ctx.forward_cfg.display();
                            ctx.back_cfg.display();
                            panic!(
                                "no region found for if block={}, then block={}, else block={}, merge block={}",
                                current_block, then_block, else_block, immediate_post_dominator
                            )
                        });
                let else_region =
                    reconstruct_region(ctx, else_block, Some(immediate_post_dominator));
                blocks.push(
                    StructuredBlock::IfThenElse {
                        cond_at: ctx.block_bounds(current_block).unwrap().1,
                        then_branch: Box::new(then_region),
                        else_branch: else_region.map(Box::new),
                    }
                    .optimize_to_chain(),
                );
                current_block = immediate_post_dominator;
            }
            (_, [next]) => {
                current_block = *next;
            }
            (_, []) => {
                break;
            }
            (_, [..]) => {
                ctx.forward_cfg.display();
                ctx.back_cfg.display();
                unimplemented!(
                    "unexpected number of successors for block {}",
                    current_block
                );
            }
        }
    }

    match blocks.len() {
        0 => None,
        1 => blocks.pop(),
        _ => Some(StructuredBlock::Seq(blocks)),
    }
}
