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
/// This function treats DUMMY_EXIT (block 1) as a terminal block that cannot reach any other blocks.
pub fn can_reach(cfg: &StacklessControlFlowGraph, start: BlockId, target: BlockId) -> bool {
    const DUMMY_EXIT: BlockId = 1;

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
        // Stop traversal at DUMMY_EXIT - it's a terminal block
        if current_block == DUMMY_EXIT {
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

/// Checks if a branch terminates (ends with abort/return) without continuing to normal code.
/// A branch terminates if ALL paths from it lead ONLY to DUMMY_EXIT and no other blocks.
///
/// Returns true if the branch terminates (abort/return), false otherwise.
pub fn branch_terminates(
    cfg: &StacklessControlFlowGraph,
    start: BlockId,
) -> bool {
    const DUMMY_EXIT: BlockId = 1;

    // A branch terminates if it has no non-exit successors
    // We do a breadth-first search and check if we reach any block other than DUMMY_EXIT
    let mut work: Vec<BlockId> = vec![start];
    let mut seen: BTreeSet<BlockId> = BTreeSet::new();

    while let Some(current_block) = work.pop() {
        if !seen.insert(current_block) {
            continue;
        }

        // If we reach DUMMY_EXIT, skip it (this is expected for terminating branches)
        if current_block == DUMMY_EXIT {
            continue;
        }

        let successors = cfg.successors(current_block);

        // If this block has successors other than DUMMY_EXIT, the branch doesn't terminate
        for next_block in successors {
            if *next_block == DUMMY_EXIT {
                // Expected for terminating branches
                continue;
            }

            // Found a non-exit successor - branch continues normally
            return false;
        }

        // Add successors to worklist (only DUMMY_EXIT at this point)
        for next_block in successors {
            if !seen.contains(next_block) {
                work.push(*next_block);
            }
        }
    }

    // All paths lead only to DUMMY_EXIT
    true
}

/// Finds the merge point for an if-then-else branch structure.
///
/// This function properly handles three cases:
/// 1. Both branches converge: Use IPD (immediate post-dominator)
/// 2. One branch terminates (abort/return): No merge point, return None
/// 3. Degenerate case (then == else): Use that block as merge
///
/// For case 2, the caller must handle the surviving branch as "rest of current region"
/// rather than expecting a merge point.
pub fn find_merge_point(
    fwd_cfg: &StacklessControlFlowGraph,
    back_cfg: &StacklessControlFlowGraph,
    branch_block: BlockId,
    then_block: BlockId,
    else_block: BlockId,
) -> Option<BlockId> {
    // Check if then and else are the same (degenerate case)
    if then_block == else_block {
        return Some(then_block);
    }

    // Try to find IPD merge point
    let ipd_merge = StacklessControlFlowGraph::find_immediate_post_dominator(back_cfg, branch_block);

    // CRITICAL: DUMMY_EXIT (block 1) is NOT a valid merge point!
    // It's just a terminal marker. If IPD is DUMMY_EXIT, we need to check for
    // terminating branches and find the actual continuation.
    const DUMMY_EXIT: BlockId = 1;

    if let Some(merge) = ipd_merge {
        if merge == DUMMY_EXIT {
            // Don't use DUMMY_EXIT as a merge - fall through to termination check
        } else {
            // IPD found a merge - verify both branches reach it
            let then_reaches = can_reach(fwd_cfg, then_block, merge);
            let else_reaches = can_reach(fwd_cfg, else_block, merge);

            if then_reaches && else_reaches {
                return Some(merge);
            }
        }
    }

    // Check if either branch terminates
    // For terminating branches, we use the surviving branch's continuation as the "merge"
    let then_terminates = branch_terminates(fwd_cfg, then_block);
    let else_terminates = branch_terminates(fwd_cfg, else_block);

    if then_terminates && else_terminates {
        // Both branches terminate - no merge point
        return None;
    }

    if then_terminates {
        // Then terminates, else continues - return None so reconstructor handles it
        return None;
    }

    if else_terminates {
        // Else terminates, then continues - return None so reconstructor handles it
        return None;
    }

    // Neither terminates but no IPD - this shouldn't happen in well-formed code
    debug!("[find_merge] WARNING: no IPD and neither branch terminates");
    ipd_merge
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
