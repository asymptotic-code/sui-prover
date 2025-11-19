// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0
use crate::stackless_bytecode::{Bytecode, Label};
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use log::{debug, error};
use move_binary_format::file_format::CodeOffset;
use std::collections::{BTreeMap, BTreeSet};

use super::helpers::*;
use super::types::StructuredBlock;
use super::dominance::PhiPlacement;
use crate::graph::NaturalLoop;

/// The context for control flow reconstruction
struct ReconstructionContext<'ctx> {
    code: &'ctx [Bytecode],
    forward_cfg: &'ctx StacklessControlFlowGraph,
    back_cfg: &'ctx StacklessControlFlowGraph,
    visited: &'ctx mut BTreeSet<BlockId>,
    phi_placement: &'ctx PhiPlacement,
}

/// Reconstructs control flow from basic blocks into a structured representation.
pub fn reconstruct_control_flow(code: &[Bytecode]) -> Vec<StructuredBlock> {
    // CRITICAL: Use ignore_aborts=true for forward CFG so that abort paths DON'T go to DUMMY_EXIT
    // This allows find_merge_point to correctly identify merge points when one branch aborts
    let forward_cfg = StacklessControlFlowGraph::new_forward_with_options(code, true);
    let back_cfg = StacklessControlFlowGraph::new_backward_with_options(code, false, true);

    // Compute formal phi-node placement using dominance frontiers
    let phi_placement = PhiPlacement::compute(code, &forward_cfg);

    let mut visited: BTreeSet<BlockId> = BTreeSet::new();

    let mut ctx = ReconstructionContext {
        code,
        forward_cfg: &forward_cfg,
        back_cfg: &back_cfg,
        visited: &mut visited,
        phi_placement: &phi_placement,
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
        result = fallback_flat_blocks(&forward_cfg);
    }

    // Compute natural loops from the CFG
    let natural_loops = compute_natural_loops_from_cfg(&forward_cfg);

    // Apply loop detection to convert IfThenElse with back-edges into While loops
    result = result.into_iter()
        .map(|block| block.detect_loops(code, &natural_loops))
        .collect();

    result
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
        return None;
    }

    // Check if start equals stop_block at the very beginning
    if Some(start) == stop_block {
        debug!(
            "[reconstruct_region] Start block {} equals stop_block, returning None immediately",
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

        if let Bytecode::Branch(_, tlabel, elabel, _cond) = instr {
            if !is_conditional_merge_pattern(ctx, upper, *tlabel, *elabel, &labels) {
                // Mark all blocks processed so far as visited before handling branch
                // This prevents infinite recursion when recursive calls encounter these blocks
                for &block in &local {
                    if Some(block) != stop_block {
                        ctx.visited.insert(block);
                    }
                }
                handle_block_ending_branch(
                    ctx, &mut seq, cursor, lower, upper, *tlabel, *elabel, &labels, stop_pc,
                    stop_block,
                );
                break
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

/// Computes natural loops from the CFG using dominator analysis.
/// Returns loops with CodeOffsets instead of BlockIds for easier comparison with bytecode.
fn compute_natural_loops_from_cfg(cfg: &StacklessControlFlowGraph) -> Vec<NaturalLoop<CodeOffset>> {
    // Extract nodes and edges from the CFG
    let entry = cfg.entry_block();
    let nodes = cfg.blocks();
    let edges: Vec<(BlockId, BlockId)> = nodes
        .iter()
        .flat_map(|&block| {
            cfg.successors(block).iter().map(move |&succ| (block, succ))
        })
        .collect();

    // Create a Graph structure for dominator analysis
    let graph = crate::graph::Graph::new(entry, nodes, edges);

    // Compute natural loops (returns None if graph is irreducible)
    let block_loops = graph.compute_reducible().unwrap_or_else(Vec::new);

    // Convert BlockId-based loops to CodeOffset-based loops
    block_loops.into_iter().filter_map(|nl| {
        let header_pc = StacklessControlFlowGraph::block_start_pc(cfg, nl.loop_header)?;
        let latch_pc = StacklessControlFlowGraph::block_start_pc(cfg, nl.loop_latch)?;
        let body_pcs: BTreeSet<CodeOffset> = nl.loop_body.iter()
            .filter_map(|&block| StacklessControlFlowGraph::block_start_pc(cfg, block))
            .collect();

        Some(NaturalLoop {
            loop_header: header_pc,
            loop_latch: latch_pc,
            loop_body: body_pcs,
        })
    }).collect()
}

/// Returns the (lower, upper) instruction bounds of a basic block, or `None`
/// for dummy blocks.
fn block_bounds(ctx: &ReconstructionContext, cursor: BlockId) -> Option<(CodeOffset, CodeOffset)> {
    match ctx.forward_cfg.content(cursor) {
        BlockContent::Basic { lower, upper } => Some((*lower, *upper)),
        BlockContent::Dummy => None,
    }
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
            error!("CFG reconstruct: failed to resolve then label; emitting Basic");
            emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
            return true;
        }
    };

    let else_block = match resolve_label_block(ctx.code, ctx.forward_cfg, elabel) {
        Some(b) => b,
        None => {
            error!("CFG reconstruct: failed to resolve else label; emitting Basic");
            emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
            return true;
        }
    };

    // First find the merge point to check termination against
    let merge_block_opt = find_merge_point(ctx.forward_cfg, ctx.back_cfg, cursor, then_block, else_block);

    // CRITICAL FIX: Always check actual branch termination - don't assume!
    // find_merge_point returns None for several cases:
    // 1. Both branches terminate (no continuation)
    // 2. One branch terminates, other has nested structure (should reconstruct fully)
    // We must check actual termination to distinguish these cases.
    let then_terminates = branch_terminates(ctx.forward_cfg, then_block);
    let else_terminates = branch_terminates(ctx.forward_cfg, else_block);

    // CRITICAL FIX: Handle terminating branch cases properly
    // When one branch terminates and merge_block_opt is None, it means the non-terminating
    // branch should be reconstructed fully (including nested structures) as the else_branch.
    let (merge_block_for_terminating, both_terminate) = if then_terminates || else_terminates {
        if then_terminates && else_terminates {
            // CRITICAL: Both branches terminate - STILL CREATE THE IF-THEN-ELSE STRUCTURE!
            // Just don't add any continuation after it.
            (None, true)  // No merge, both terminate
        } else {
            // One branch terminates, one continues
            // If merge_block_opt is Some, use it. If None, non-terminating branch has nested structure.
            match merge_block_opt {
                Some(merge) => {
                    (Some(merge), false)
                }
                None => {
                    (None, false)  // No merge block, non-terminating branch has nested structure
                }
            }
        }
    } else {
        // Normal merge case - both branches converge
        match merge_block_opt {
            Some(merge) => (Some(merge), false),
            None => {
                error!("CFG reconstruct: no merge found for non-terminating branches; emitting Basic");
                emit_basic_block_with_trim(ctx, seq, cursor, lower, upper, stop_pc, labels);
                return true;
            }
        }
    };

    // Emit pre-branch part
    if lower < upper {
        let pre_lower = lower;
        let pre_upper = trim_jump_to_merge(
            ctx.code,
            ctx.forward_cfg,
            pre_lower,
            upper - 1,
            merge_block_for_terminating,
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

    // Build branches (cursor is already marked as visited by caller)
    let (then_struct, else_struct) = if both_terminate {
        // Both branches terminate - reconstruct both with None as stop (they end with return/abort)
        let then_struct = reconstruct_region(ctx, then_block, None);
        let else_struct = reconstruct_region(ctx, else_block, None);
        (then_struct, else_struct)
    } else if then_terminates && !else_terminates {
        // Then terminates, else continues - else should stop at merge block
        let then_struct = reconstruct_region(ctx, then_block, merge_block_for_terminating);
        let else_struct = reconstruct_region(ctx, else_block, merge_block_for_terminating);
        (then_struct, else_struct)
    } else if else_terminates && !then_terminates {
        // Else terminates, then continues - then should stop at merge block
        let then_struct = reconstruct_region(ctx, then_block, merge_block_for_terminating);
        let else_struct = reconstruct_region(ctx, else_block, merge_block_for_terminating);
        (then_struct, else_struct)
    } else {
        // Normal merge - both branches stop at merge point
        let merge_block = merge_block_for_terminating.unwrap();  // Safe because neither terminates
        let then_struct = reconstruct_region(ctx, then_block, Some(merge_block));
        let else_struct = if else_block == merge_block {
            None
        } else {
            reconstruct_region(ctx, else_block, Some(merge_block))
        };
        (then_struct, else_struct)
    };

    // Extract condition temp from the Branch instruction
    let cond_temp = if let Some(Bytecode::Branch(_, _, _, temp)) = ctx.code.get(upper as usize) {
        *temp
    } else {
        0 // Fallback (should not happen for well-formed bytecode)
    };

    // Compute phi-variables using formal dominance analysis
    // Only compute phi-vars if there's actually a merge point (not when both branches terminate)
    let phi_variables = if let Some(merge_block) = merge_block_for_terminating {
        compute_phi_variables_for_merge(
            ctx,
            merge_block,
            &then_struct,
            &else_struct,
        )
    } else {
        vec![]  // No merge point, no phi-variables
    };

    let if_block = StructuredBlock::IfThenElse {
        cond_at: upper,
        cond_temp,
        then_branch: Box::new(then_struct.unwrap_or(StructuredBlock::Seq(vec![]))),
        else_branch: else_struct.map(Box::new),
        phi_variables,
    };
    seq.push(if_block.optimize_to_chain());

    // CRITICAL FIX: When one branch terminates and merge_block_for_terminating is None,
    // the non-terminating branch already includes all nested structure.
    // Do NOT add continuation - it's already inside the branch!
    //
    // When merge_block_for_terminating is Some, only add continuation if not at stop_block.
    if let Some(merge_block) = merge_block_for_terminating {
        let should_continue = Some(merge_block) != stop_block;

        if should_continue && !ctx.visited.contains(&merge_block) {
            if let Some(rest) = reconstruct_region(ctx, merge_block, stop_block) {
                match rest {
                    StructuredBlock::Seq(v) => seq.extend(v),
                    other => seq.push(other),
                }
            }
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
                    if jpc == spc {
                        // Jump to stop_block should be trimmed
                        if upper > lower {
                            upper -= 1;
                        } else {
                            // Block is ONLY a Jump to stop_block - skip emitting entirely
                            return;
                        }
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
                    if jpc == spc {
                        // Jump to stop_block should be trimmed
                        if upper > lower {
                            upper -= 1;
                        } else {
                            // Block is ONLY a Jump to stop_block - skip emitting entirely
                            return;
                        }
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

/// Compute phi-variables for an if-statement merge using formal dominance analysis.
///
/// This function:
/// 1. Queries the phi placement to see which variables need phi-nodes at merge_block
/// 2. For each such variable, finds the last assigned value in the structured branches
/// 3. Creates IfPhiVariable entries with the actual values
fn compute_phi_variables_for_merge(
    ctx: &ReconstructionContext,
    merge_block: BlockId,
    then_struct: &Option<StructuredBlock>,
    else_struct: &Option<StructuredBlock>,
) -> Vec<super::types::IfPhiVariable> {
    use super::types::IfPhiVariable;

    // Get variables that need phi-nodes at the merge point
    let phi_vars = match ctx.phi_placement.get_phi_variables(merge_block) {
        Some(vars) => vars,
        None => return vec![],
    };

    // For each phi variable, find the value coming from each branch
    let result: Vec<_> = phi_vars
        .iter()
        .filter_map(|&var| {
            let then_value = if let Some(ref then_block) = then_struct {
                find_last_value_in_structured_block(then_block, var, ctx.code)
            } else {
                var // Empty then-branch, value unchanged
            };

            let else_value = if let Some(ref else_block) = else_struct {
                find_last_value_in_structured_block(else_block, var, ctx.code)
            } else {
                var // Empty else-branch, value unchanged
            };

            // Only create phi-variable if the values are different
            if then_value != else_value {
                Some(IfPhiVariable {
                    temp: var,
                    then_value,
                    else_value,
                })
            } else {
                None
            }
        })
        .collect();

    result
}

/// Find the last value assigned to a variable in a structured block.
///
/// This recursively searches through the structured block tree to find the last
/// assignment to `var`. Works with nested If/While/Sequence structures.
fn find_last_value_in_structured_block(
    block: &StructuredBlock,
    var: usize,
    code: &[Bytecode],
) -> usize {
    match block {
        StructuredBlock::Basic { lower, upper } => {
            // Scan backwards through the bytecode range
            for pc in (*lower..=*upper).rev() {
                if let Some(bytecode) = code.get(pc as usize) {
                    match bytecode {
                        Bytecode::Assign(_, dst, src, _) if *dst == var => {
                            return *src;
                        }
                        Bytecode::Load(_, dst, _) if *dst == var => {
                            return var;
                        }
                        Bytecode::Call(_, dests, _, _, _) if dests.contains(&var) => {
                            return var;
                        }
                        _ => {}
                    }
                }
            }
            var // Not assigned in this block
        }

        StructuredBlock::Seq(blocks) => {
            // Search backwards through sequence
            for block in blocks.iter().rev() {
                let value = find_last_value_in_structured_block(block, var, code);
                if value != var {
                    return value; // Found an assignment
                }
            }
            var // Not found in sequence
        }

        StructuredBlock::IfThenElse {
            then_branch,
            else_branch,
            phi_variables,
            ..
        } => {
            // Check if this if-statement has a phi-variable for our var
            for phi in phi_variables {
                if phi.temp == var {
                    // This if-statement defines var through a phi
                    // Return var itself (the phi result)
                    return var;
                }
            }

            // If no phi, the variable is not defined in this if
            // Try checking the branches (though this shouldn't happen with correct dominance)
            if let Some(else_block) = else_branch {
                let else_val = find_last_value_in_structured_block(else_block, var, code);
                if else_val != var {
                    return else_val;
                }
            }

            let then_val = find_last_value_in_structured_block(then_branch, var, code);
            if then_val != var {
                return then_val;
            }

            var
        }

        StructuredBlock::While { body, .. } => {
            // Search in loop body
            find_last_value_in_structured_block(body, var, code)
        }

        StructuredBlock::IfElseChain { branches, else_branch } => {
            // Check else branch first (last in execution order)
            if let Some(else_block) = else_branch {
                let value = find_last_value_in_structured_block(else_block, var, code);
                if value != var {
                    return value;
                }
            }

            // Check branches in reverse order
            for (_, branch) in branches.iter().rev() {
                let value = find_last_value_in_structured_block(branch, var, code);
                if value != var {
                    return value;
                }
            }

            var
        }
    }
}
