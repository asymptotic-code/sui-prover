// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

use crate::stackless_bytecode::{Bytecode, Label};
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use log::debug;
use move_binary_format::file_format::CodeOffset;
use std::collections::BTreeSet;

/// Finds the block for a given label, or None if one isn't found.
pub fn resolve_label_block(
    code: &[Bytecode],
    cfg: &StacklessControlFlowGraph,
    label: Label,
) -> Option<BlockId> {
    let labels = Bytecode::label_offsets(code);
    let pc = *labels.get(&label)?;
    let block = StacklessControlFlowGraph::pc_to_block(cfg, pc)?;
    Some(block)
}

/// Tries to find the fallthrough successor, the next sequential successor.
/// Just returns the first successor if it's a Dummy block or if the next block isn't a successor.
pub fn prefer_fallthrough_successor(
    cfg: &StacklessControlFlowGraph,
    from: BlockId,
) -> Option<BlockId> {
    let fallthrough_pc = match cfg.content(from) {
        BlockContent::Basic { upper, .. } => *upper + 1,
        BlockContent::Dummy => {
            // For dummy blocks it has to return the first successor
            return cfg.successors(from).first().copied();
        }
    };

    cfg.successors(from).iter()
        .find(|successor| StacklessControlFlowGraph::block_start_pc(cfg, **successor)
            .map(|start_pc| start_pc == fallthrough_pc).unwrap_or(false))
        .cloned()
        .or_else(|| cfg.successors(from).first().copied())
}

/// Determines if start can reach target along the cfg by breadth-first searching the graph.
pub fn can_reach(cfg: &StacklessControlFlowGraph, start: BlockId, target: BlockId) -> bool {
    if start == target {
        return true;
    }
    let mut work: Vec<BlockId> = vec![start];
    let mut seen: BTreeSet<BlockId> = BTreeSet::new();
    while let Some(current_block) = work.pop() {
        if current_block == target {
            return true;
        }
        if !seen.insert(current_block) {
            continue;
        }
        for next_block in cfg.successors(current_block) {
            if !seen.contains(next_block) {
                work.push(*next_block);
            }
        }
    }
    false
}

/// Returns the first postdominator, if none exists, then uses either the else or then to merge
/// depending on which can be reached by the other.
pub fn find_merge_point(
    fwd_cfg: &StacklessControlFlowGraph,
    back_cfg: &StacklessControlFlowGraph,
    branch_block: BlockId,
    then_block: BlockId,
    else_block: BlockId,
) -> Option<BlockId> {
    let mut merge_block = StacklessControlFlowGraph::find_immediate_post_dominator(back_cfg, branch_block);

    debug!(
        "[find_merge] branch_block={} then={} else={} IPD={:?}",
        branch_block, then_block, else_block, merge_block
    );

    // Check if then and else are the same (degenerate case)
    if then_block == else_block {
        debug!("[find_merge] then and else are the same block, using it as merge");
        return Some(then_block);
    }

    if merge_block.is_none() {
        let then_reaches_else = can_reach(fwd_cfg, then_block, else_block);
        let else_reaches_then = can_reach(fwd_cfg, else_block, then_block);
        debug!(
            "[find_merge] then->else={} else->then={}",
            then_reaches_else, else_reaches_then
        );

        if then_reaches_else {
            merge_block = Some(else_block);
        } else if else_reaches_then {
            merge_block = Some(then_block);
        }
    }

    debug!("[find_merge] final merge={:?}", merge_block);
    merge_block
}

/// Automatically skips blocks if there's only a single successor, no actual bytecode, and it's not
/// the very first label.
pub fn should_suppress_label_block(
    code: &[Bytecode],
    back_cfg: &StacklessControlFlowGraph,
    block_id: BlockId,
    lower: CodeOffset,
    upper: CodeOffset,
    seq_is_empty: bool,
) -> bool {
    let is_label_only = lower == upper && matches!(code[lower as usize], Bytecode::Label(..));
    let single_pred = back_cfg.successors(block_id).len() == 1;
    is_label_only && single_pred && !seq_is_empty
}

/// Trims the jump to the merge block if it's the last instruction in the block.
pub fn trim_jump_to_merge(
    code: &[Bytecode],
    forward_cfg: &StacklessControlFlowGraph,
    lower: CodeOffset,
    mut upper: CodeOffset,
    merge_block: Option<BlockId>,
) -> CodeOffset {
    let Some(merge_start_pc) =
        merge_block.and_then(|merge_block| StacklessControlFlowGraph::block_start_pc(forward_cfg, merge_block)) else {
        return upper;
    };

    if upper < lower {
        return upper;
    }

    let Bytecode::Jump(_, jlabel) = &code[upper as usize] else {
        return upper;
    };

    let labels = Bytecode::label_offsets(code);
    if let Some(&jpc) = labels.get(jlabel) {
        if jpc == merge_start_pc && upper > lower {
            upper -= 1;
        }
    }

    upper
}
