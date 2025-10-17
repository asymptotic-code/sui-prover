// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0
use crate::stackless_bytecode::{Bytecode, Label};
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use log::{debug, warn};
use move_binary_format::file_format::CodeOffset;
use std::collections::{BTreeMap, BTreeSet};

use super::helpers::*;
use super::types::StructuredBlock;

/// The context for control flow reconstruction
struct ReconstructionContext<'ctx> {
    code: &'ctx [Bytecode],
    forward_cfg: &'ctx StacklessControlFlowGraph,
    back_cfg: &'ctx StacklessControlFlowGraph,
    visited: &'ctx mut BTreeSet<BlockId>,
}

/// Reconstructs control flow from basic blocks into a structured representation.
pub fn reconstruct_control_flow(code: &[Bytecode]) -> Vec<StructuredBlock> {
    let forward_cfg = StacklessControlFlowGraph::new_forward(code);
    let back_cfg = StacklessControlFlowGraph::new_backward(code, false);
    let mut visited: BTreeSet<BlockId> = BTreeSet::new();

    let mut ctx = ReconstructionContext {
        code,
        forward_cfg: &forward_cfg,
        back_cfg: &back_cfg,
        visited: &mut visited,
    };

    let mut result: Vec<StructuredBlock> = Vec::new();
    let entry = forward_cfg.entry_block();

    // Recursively reconstruct from the entry
    if let Some(s) = reconstruct_region(&mut ctx, entry, None) {
        match s {
            StructuredBlock::Seq(v) => {
                result.extend(v);
            }
            other => {
                result.push(other);
            }
        }
    }

    if result.is_empty() {
        fallback_flat_blocks(&forward_cfg)
    } else {
        result
    }
}

/// Translates all CFG blocks into a basic flat StructuredBlock vec.
fn fallback_flat_blocks(
    forward_cfg: &StacklessControlFlowGraph,
) -> Vec<StructuredBlock> {
    let mut flat: Vec<StructuredBlock> = Vec::new();
    for block in forward_cfg.blocks() {
        if let BlockContent::Basic { lower, upper } = forward_cfg.content(block) {
            flat.push(StructuredBlock::Basic {
                lower: *lower,
                upper: *upper,
            });
        }
    }
    if flat.len() <= 1 {
        flat
    } else {
        vec![StructuredBlock::Seq(flat)]
    }
}

/// Recursively reconstructs a region into `StructuredBlock`s.
///
/// - Starts at `start` and continues following fallthrough edges until it reaches
///   `stop_block` (exclusive), encounters a back-edge (loop), or cannot advance.
/// - Prefers structuring mid-block branches, then block-ending branches.
/// - Emits `Basic` blocks when structuring does not apply.
/// - Uses a local set to detect loops and a global `visited` set to avoid
///   reprocessing in outer calls.
fn reconstruct_region(
    ctx: &mut ReconstructionContext,
    start: BlockId,
    stop_block: Option<BlockId>,
) -> Option<StructuredBlock> {
    // Skip if already processed by an ancestor call
    if ctx.visited.contains(&start) {
        debug!(
            "[reconstruct_region] Block {} already visited globally, skipping",
            start
        );
        return None;
    }

    let mut seq: Vec<StructuredBlock> = Vec::new();
    let mut cursor = start;
    let mut local: BTreeSet<BlockId> = BTreeSet::new();
    let labels = Bytecode::label_offsets(ctx.code);
    let stop_pc = stop_block
        .and_then(|b| StacklessControlFlowGraph::block_start_pc(ctx.forward_cfg, b));

    while !local.contains(&cursor) {
        if Some(cursor) == stop_block {
            debug!("[reconstruct_region] Stopping at stop_block: {}", cursor);
            break;
        }
        if ctx.visited.contains(&cursor) {
            debug!(
                "[reconstruct_region] Block {} already visited globally during iteration, stopping",
                cursor
            );
            break;
        }

        local.insert(cursor);

        // Skip dummy blocks by falling through
        if ctx.forward_cfg.is_dummmy(cursor) {
            if let Some(next) = prefer_fallthrough_successor(ctx.forward_cfg, cursor) {
                cursor = next;
                continue;
            }
            break;
        }

        let (lower, upper) = match block_bounds(ctx, cursor) {
            Some(bounds) => bounds,
            None => {
                if let Some(next) = prefer_fallthrough_successor(ctx.forward_cfg, cursor) {
                    cursor = next;
                    continue;
                }
                break;
            }
        };

        let instr = &ctx.code[upper as usize];

        // Try mid-block branch first if the block doesn't end in a Branch
        if !matches!(instr, Bytecode::Branch(..)) {
            if let Some(cond_at) = find_mid_block_branch(ctx.code, lower, upper) {
                if handle_mid_block_branch(ctx, &mut seq, cursor, lower, upper, cond_at, stop_block)
                {
                    break;
                }
            }
        }

        // Try block-ending branch if present and not part of the conditional-merge pattern
        if let Bytecode::Branch(_, tlabel, elabel, _cond) = instr {
            if !is_conditional_merge_pattern(ctx, upper, *tlabel, *elabel, &labels) {
                if handle_block_ending_branch(
                    ctx, &mut seq, cursor, lower, upper, *tlabel, *elabel, &labels, stop_pc,
                    stop_block,
                ) {
                    break;
                }

                // Fall through could not be structured; advance
                if let Some(next) = prefer_fallthrough_successor(ctx.forward_cfg, cursor) {
                    cursor = next;
                    continue;
                }
                break;
            }
        }

        // Default: emit basic block and advance
        emit_basic_block(ctx, &mut seq, cursor, lower, upper, stop_pc);

        if let Some(next) = prefer_fallthrough_successor(ctx.forward_cfg, cursor) {
            if Some(next) == stop_block {
                break;
            }
            if local.contains(&next) {
                debug!(
                    "[reconstruct_region] Detected back edge from {} to {} (loop), stopping",
                    cursor, next
                );
                break;
            }
            cursor = next;
        } else {
            break;
        }
    }

    for block in local {
        if Some(block) != stop_block {
            ctx.visited.insert(block);
        }
    }

    finalize_sequence(seq)
}

/// Returns the (lower, upper) instruction bounds of a basic block, or `None`
/// for dummy blocks.
fn block_bounds(ctx: &ReconstructionContext, cursor: BlockId) -> Option<(CodeOffset, CodeOffset)> {
    match ctx.forward_cfg.content(cursor) {
        BlockContent::Basic { lower, upper } => Some((*lower, *upper)),
        BlockContent::Dummy => None,
    }
}

/// Finds the first `Branch` within the range `[lower, upper]` of a single block.
/// Returns `Some(pc)` if one exists; otherwise `None`.
fn find_mid_block_branch(
    code: &[Bytecode],
    lower: CodeOffset,
    upper: CodeOffset,
) -> Option<CodeOffset> {
    for pc in lower..=upper {
        if matches!(code[pc as usize], Bytecode::Branch(..)) {
            return Some(pc);
        }
    }
    None
}

/// Detects the ConditionalMergeInsertion pattern: a `Branch` whose join point
/// is followed by a synthesized `IfThenElse` operation. Such patterns are left
/// as basic blocks to avoid double-structuring.
fn is_conditional_merge_pattern(
    ctx: &ReconstructionContext,
    branch_pc: CodeOffset,
    then_label: Label,
    else_label: Label,
    labels: &BTreeMap<Label, CodeOffset>,
) -> bool {
    use crate::stackless_bytecode::Operation;

    // Find the merge point - it's typically the instruction after both branches
    let then_pc = labels.get(&then_label).copied();
    let else_pc = labels.get(&else_label).copied();

    if then_pc.is_none() || else_pc.is_none() {
        return false;
    }

    let then_pc = then_pc.unwrap();
    let else_pc = else_pc.unwrap();

    // Look for the merge point by checking a few instructions after the branch
    // The pattern is: Branch -> then/else -> merge label -> if_then_else operation
    let search_start = branch_pc + 1;
    let search_end = (branch_pc + 50).min(ctx.code.len() as CodeOffset);

    for pc in search_start..search_end {
        if let Some(Bytecode::Call(_, _, Operation::IfThenElse, _, _)) = ctx.code.get(pc as usize) {
            // Found an if_then_else operation near the branch
            // Check if it's after both then and else paths
            if pc > then_pc && pc > else_pc {
                debug!(
                    "[is_conditional_merge_pattern] Found if_then_else at pc {} after Branch at pc {} (then={}, else={})",
                    pc, branch_pc, then_pc, else_pc
                );
                return true;
            }
        }
    }

    false
}

/// Attempts to structure a mid-block `Branch` located at `cond_at` within
/// `[lower, upper]`. Emits any pre-branch `Basic` part, constructs the
/// `IfThenElse` (and optionally optimizes to chain), and appends the remainder
/// after the merge. Returns `true` if structuring succeeded and control should
/// return to the caller.
fn handle_mid_block_branch(
    ctx: &mut ReconstructionContext,
    seq: &mut Vec<StructuredBlock>,
    cursor: BlockId,
    lower: CodeOffset,
    upper: CodeOffset,
    cond_at: CodeOffset,
    stop_block: Option<BlockId>,
) -> bool {
    if cond_at >= upper {
        return false;
    }

    debug!(
        "[reconstructor] considering mid-block Branch at pc {} in block {}",
        cond_at, cursor
    );

    let Bytecode::Branch(_, tlabel, elabel, _cond) = &ctx.code[cond_at as usize] else {
        return false;
    };

    let Some(then_block) = resolve_label_block(ctx.code, ctx.forward_cfg, *tlabel) else {
        return false;
    };
    let Some(else_block) = resolve_label_block(ctx.code, ctx.forward_cfg, *elabel) else {
        return false;
    };

    let merge_block = find_merge_point(ctx.forward_cfg, ctx.back_cfg, cursor, then_block, else_block);
    debug!(
        "[reconstructor] mid-block IPD for block {} = {:?}",
        cursor, merge_block
    );

    let Some(merge_block) = merge_block else {
        debug!("[reconstructor] mid-block structuring skipped: no merge found");
        return false;
    };

    debug!(
        "[reconstructor] structuring mid-block IfThenElse at pc={} merge={} then={} else={}",
        cond_at, merge_block, then_block, else_block
    );

    // Emit pre-branch part
    if lower < cond_at {
        let pre_lower = lower;
        let pre_upper = trim_jump_to_merge(
            ctx.code,
            ctx.forward_cfg,
            pre_lower,
            cond_at - 1,
            Some(merge_block),
        );

        if !should_suppress_label_block(
            ctx.code,
            ctx.back_cfg,
            cursor,
            pre_lower,
            pre_upper,
            seq.is_empty(),
        ) {
            seq.push(StructuredBlock::Basic {
                lower: pre_lower,
                upper: pre_upper,
            });
        }
    }

    // Build branches
    let then_struct = reconstruct_region(ctx, then_block, Some(merge_block));
    let else_struct = if else_block == merge_block {
        None
    } else {
        reconstruct_region(ctx, else_block, Some(merge_block))
    };

    debug!(
        "[reconstructor] EMIT mid-block IfThenElse cond_at={} then={} else={} merge={}",
        cond_at, then_block, else_block, merge_block
    );

    let if_block = StructuredBlock::IfThenElse {
        cond_at,
        then_branch: Box::new(then_struct.unwrap_or(StructuredBlock::Seq(vec![]))),
        else_branch: else_struct.map(Box::new),
    };
    seq.push(if_block.optimize_to_chain());

    // Continue from merge
    if let Some(rest) = reconstruct_region(ctx, merge_block, stop_block) {
        match rest {
            StructuredBlock::Seq(v) => seq.extend(v),
            other => seq.push(other),
        }
    }

    true
}

/// Attempts to structure a block-ending `Branch` at `upper` for the current
/// block. Emits any pre-branch `Basic` part, constructs the `IfThenElse`
/// (and optionally optimizes to chain), and appends the remainder after the
/// merge. Returns `true` if structuring succeeded and control should return to
/// the caller.
fn handle_block_ending_branch(
    ctx: &mut ReconstructionContext,
    seq: &mut Vec<StructuredBlock>,
    cursor: BlockId,
    lower: CodeOffset,
    upper: CodeOffset,
    tlabel: Label,
    elabel: Label,
    labels: &BTreeMap<Label, CodeOffset>,
    stop_pc: Option<CodeOffset>,
    stop_block: Option<BlockId>,
) -> bool {
    let then_block = match resolve_label_block(ctx.code, ctx.forward_cfg, tlabel) {
        Some(b) => b,
        None => {
            warn!("CFG reconstruct: failed to resolve then label; emitting Basic");
            emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
            return false;
        }
    };

    let else_block = match resolve_label_block(ctx.code, ctx.forward_cfg, elabel) {
        Some(b) => b,
        None => {
            warn!("CFG reconstruct: failed to resolve else label; emitting Basic");
            emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
            return false;
        }
    };

    let merge_block = find_merge_point(ctx.forward_cfg, ctx.back_cfg, cursor, then_block, else_block);

    let Some(merge_block) = merge_block else {
        debug!("CFG reconstruct: no IPD merge found; emitting Basic");
        emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
        return false;
    };

    debug!(
        "[reconstructor] structuring IfThenElse at pc={} merge={} then={} else={}",
        upper, merge_block, then_block, else_block
    );

    // Emit pre-branch part
    if lower < upper {
        let pre_lower = lower;
        let pre_upper = trim_jump_to_merge(
            ctx.code,
            ctx.forward_cfg,
            pre_lower,
            upper - 1,
            Some(merge_block),
        );

        if !should_suppress_label_block(
            ctx.code,
            ctx.back_cfg,
            cursor,
            pre_lower,
            pre_upper,
            seq.is_empty(),
        ) {
            seq.push(StructuredBlock::Basic {
                lower: pre_lower,
                upper: pre_upper,
            });
        }
    }

    // Build branches
    let then_struct = reconstruct_region(ctx, then_block, Some(merge_block));
    let else_struct = if else_block == merge_block {
        None
    } else {
        reconstruct_region(ctx, else_block, Some(merge_block))
    };

    // Verify branch at upper
    if !matches!(&ctx.code[upper as usize], Bytecode::Branch(..)) {
        warn!(
            "CFG reconstruct: expected Branch at block end pc={}, falling back to Basic",
            upper
        );
        emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
        return false;
    }

    let if_block = StructuredBlock::IfThenElse {
        cond_at: upper,
        then_branch: Box::new(then_struct.unwrap_or(StructuredBlock::Seq(vec![]))),
        else_branch: else_struct.map(Box::new),
    };
    seq.push(if_block.optimize_to_chain());

    // Continue from merge
    if let Some(rest) = reconstruct_region(ctx, merge_block, stop_block) {
        match rest {
            StructuredBlock::Seq(v) => seq.extend(v),
            other => seq.push(other),
        }
    }

    true
}

/// Emits a `StructuredBlock::Basic` for `[lower, upper]`, possibly trimming a
/// trailing jump to `stop_pc`. Suppresses label-only blocks when they have a
/// single predecessor and the current sequence is not empty (noise reduction).
fn emit_basic_block(
    ctx: &ReconstructionContext,
    seq: &mut Vec<StructuredBlock>,
    cursor: BlockId,
    lower: CodeOffset,
    mut upper: CodeOffset,
    stop_pc: Option<CodeOffset>,
) {
    if let Some(spc) = stop_pc {
        if upper >= lower {
            if let Bytecode::Jump(_, jlabel) = &ctx.code[upper as usize] {
                let labels = Bytecode::label_offsets(ctx.code);
                if let Some(&jpc) = labels.get(jlabel) {
                    if jpc == spc && upper > lower {
                        upper -= 1;
                    }
                }
            }
        }
    }

    let is_label_only = lower == upper && matches!(ctx.code[lower as usize], Bytecode::Label(..));
    let single_pred = ctx.back_cfg.successors(cursor).len() == 1;

    if !(is_label_only && single_pred && !seq.is_empty()) {
        seq.push(StructuredBlock::Basic { lower, upper });
    }
}

/// Same as `emit_basic_block`, but uses a precomputed label map provided by the
/// caller to avoid recomputing it for trimming.
fn emit_basic_block_with_trim(
    ctx: &ReconstructionContext,
    seq: &mut Vec<StructuredBlock>,
    cursor: BlockId,
    lower: CodeOffset,
    mut upper: CodeOffset,
    stop_pc: Option<CodeOffset>,
    labels: &BTreeMap<Label, CodeOffset>,
) {
    if let Some(spc) = stop_pc {
        if upper >= lower {
            if let Bytecode::Jump(_, jlabel) = &ctx.code[upper as usize] {
                if let Some(&jpc) = labels.get(jlabel) {
                    if jpc == spc && upper > lower {
                        upper -= 1;
                    }
                }
            }
        }
    }

    let is_label_only = lower == upper && matches!(ctx.code[lower as usize], Bytecode::Label(..));
    let single_pred = ctx.back_cfg.successors(cursor).len() == 1;

    if !(is_label_only && single_pred && !seq.is_empty()) {
        seq.push(StructuredBlock::Basic { lower, upper });
    }
}

/// Normalizes a sequence of structured blocks:
/// - `[]` -> `None`
/// - `[x]` -> `Some(x)`
/// - `[x, ..]` -> `Some(Seq(vec![..]))`
fn finalize_sequence(seq: Vec<StructuredBlock>) -> Option<StructuredBlock> {
    if seq.is_empty() {
        None
    } else if seq.len() == 1 {
        Some(seq.into_iter().next().unwrap())
    } else {
        Some(StructuredBlock::Seq(seq))
    }
}
