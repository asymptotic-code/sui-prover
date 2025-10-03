// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! A lightweight control-flow reconstructor that produces a structured sequence of
//! control blocks from stackless bytecode basic blocks. This is an initial version
//! which linearizes reachable basic blocks in a deterministic traversal order. It
//! provides an API surface that can later be extended to detect structured
//! conditionals and loops.

use crate::stackless_bytecode::{Bytecode, Label};
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use log::{debug, info, warn};
use move_binary_format::file_format::CodeOffset;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug)]
pub enum StructuredBlock {
    /// A straight-line sequence of bytecodes from `lower..=upper` (inclusive)
    Basic { lower: CodeOffset, upper: CodeOffset },
    /// A sequence of blocks
    Seq(Vec<StructuredBlock>),
    /// A structured if/else with the condition evaluated at `cond_at` (the Branch instruction)
    /// and structured bodies up to the merge point. `else_branch` is None for if-then.
    IfThenElse {
        cond_at: CodeOffset,
        then_branch: Box<StructuredBlock>,
        else_branch: Option<Box<StructuredBlock>>,
    },
    // Future: Loop { header: BlockId, body: Box<StructuredBlock> },
}

impl StructuredBlock {
    /// Iterate over bytecode offsets contained in this structured block, in order.
    pub fn instr_indexes<'a>(&'a self) -> Box<dyn Iterator<Item = CodeOffset> + 'a> {
        match self {
            StructuredBlock::Basic { lower, upper } => Box::new((*lower)..=(*upper)),
            StructuredBlock::Seq(blocks) => Box::new(blocks.iter().flat_map(|b| b.instr_indexes())),
            StructuredBlock::IfThenElse { cond_at: _, then_branch, else_branch } => {
                let then_iter = then_branch.instr_indexes();
                if let Some(eb) = else_branch {
                    let else_iter = eb.instr_indexes();
                    Box::new(then_iter.chain(else_iter))
                } else {
                    then_iter
                }
            }
        }
    }
}

/// Reconstructs control flow from basic blocks into a structured representation.
///
/// Current strategy: reachability-preserving linearization via BFS from the entry
/// block over the existing CFG. Dummy entry/exit nodes are skipped.
pub fn reconstruct_control_flow(code: &[Bytecode]) -> Vec<StructuredBlock> {
    let fwd_cfg = StacklessControlFlowGraph::new_forward(code);
    let back_cfg = StacklessControlFlowGraph::new_backward(code, false);

    // Cache for resolving pc -> block ids. Built on-demand via cfg.pc_to_block.
    let mut pc_to_block_cache: BTreeMap<CodeOffset, BlockId> = BTreeMap::new();

    let mut visited: BTreeSet<BlockId> = BTreeSet::new();

    // Diagnostics: count blocks that end with a Branch, any Branch, and any IfThenElse ops
    let mut branch_end_blocks = 0usize;
    let mut branch_any = 0usize;
    let mut ifthenelse_ops = 0usize;
    let mut branch_pcs: Vec<CodeOffset> = vec![];
    let mut if_pcs: Vec<CodeOffset> = vec![];
    for (pc, instr) in code.iter().enumerate() {
        match instr {
            Bytecode::Branch(..) => {
                branch_any += 1;
                branch_pcs.push(pc as CodeOffset);
            }
            Bytecode::Call(_, _, crate::stackless_bytecode::Operation::IfThenElse, _, _) => {
                ifthenelse_ops += 1;
                if_pcs.push(pc as CodeOffset);
            }
            _ => {}
        }
    }
    for b in fwd_cfg.blocks() {
        if let BlockContent::Basic { upper, .. } = fwd_cfg.content(b) {
            if let Some(instr) = code.get(*upper as usize) {
                if matches!(instr, Bytecode::Branch(..)) {
                    branch_end_blocks += 1;
                }
            }
        }
    }
    eprintln!("[reconstructor] blocks ending with Branch = {}", branch_end_blocks);
    eprintln!("[reconstructor] total Branch instr = {} at pcs = {:?}", branch_any, branch_pcs);
    eprintln!("[reconstructor] total IfThenElse ops = {} at pcs = {:?}", ifthenelse_ops, if_pcs);

    
    // Helpers

    fn resolve_label_block(
        code: &[Bytecode],
        cfg: &StacklessControlFlowGraph,
        cache: &mut BTreeMap<CodeOffset, BlockId>,
        label: Label,
    ) -> Option<BlockId> {
        let labels = Bytecode::label_offsets(code);
        let pc = *labels.get(&label)?;
        if let Some(b) = cache.get(&pc) {
            return Some(*b);
        }
        let b = StacklessControlFlowGraph::pc_to_block(cfg, pc)?;
        cache.insert(pc, b);
        Some(b)
    }

    fn prefer_fallthrough_successor(
        cfg: &StacklessControlFlowGraph,
        from: BlockId,
    ) -> Option<BlockId> {
        let (_lower, upper) = match cfg.content(from) {
            BlockContent::Basic { lower, upper } => (*lower, *upper),
            BlockContent::Dummy => return None,
        };
        let fallthrough_pc = upper + 1;
        for s in cfg.successors(from) {
            if let Some(spc) = StacklessControlFlowGraph::block_start_pc(cfg, *s) {
                if spc == fallthrough_pc {
                    return Some(*s);
                }
            }
        }
        cfg.successors(from).first().copied()
    }

    fn can_reach_without_crossing(
        cfg: &StacklessControlFlowGraph,
        start: BlockId,
        target: BlockId,
        forbidden_entry: BlockId,
    ) -> bool {
        if start == target {
            return true;
        }
        let mut work: Vec<BlockId> = vec![start];
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        while let Some(b) = work.pop() {
            if b == target {
                return true;
            }
            if !seen.insert(b) {
                continue;
            }
            if b == forbidden_entry {
                continue;
            }
            for s in cfg.successors(b) {
                if !seen.contains(s) {
                    work.push(*s);
                }
            }
        }
        false
    }

    fn can_reach(cfg: &StacklessControlFlowGraph, start: BlockId, target: BlockId) -> bool {
        if start == target {
            return true;
        }
        let mut work: Vec<BlockId> = vec![start];
        let mut seen: BTreeSet<BlockId> = BTreeSet::new();
        while let Some(b) = work.pop() {
            if b == target {
                return true;
            }
            if !seen.insert(b) {
                continue;
            }
            for s in cfg.successors(b) {
                if !seen.contains(s) {
                    work.push(*s);
                }
            }
        }
        false
    }

    // Reconstruct a region starting at block `start`, stopping before `stop_block` if provided.
    fn reconstruct_region(
        code: &[Bytecode],
        fwd_cfg: &StacklessControlFlowGraph,
        back_cfg: &StacklessControlFlowGraph,
        pc_to_block_cache: &mut BTreeMap<CodeOffset, BlockId>,
        visited: &mut BTreeSet<BlockId>,
        start: BlockId,
        stop_block: Option<BlockId>,
    ) -> Option<StructuredBlock> {
        let mut seq: Vec<StructuredBlock> = Vec::new();
        let mut cursor = start;
        let mut local: BTreeSet<BlockId> = BTreeSet::new(); // recursion guard only
        let labels = Bytecode::label_offsets(code);
        let stop_pc: Option<CodeOffset> = stop_block
            .and_then(|b| StacklessControlFlowGraph::block_start_pc(fwd_cfg, b));

        while !local.contains(&cursor) {
            if Some(cursor) == stop_block {
                break;
            }
            local.insert(cursor);

            if fwd_cfg.is_dummmy(cursor) {
                // advance deterministically
                if let Some(next) = prefer_fallthrough_successor(fwd_cfg, cursor) {
                    cursor = next;
                    continue;
                }
                break;
            }

            let (lower, upper) = match fwd_cfg.content(cursor) {
                BlockContent::Basic { lower, upper } => (*lower, *upper),
                BlockContent::Dummy => unreachable!(),
            };
            eprintln!(
                "[reconstructor] visiting block id={} bounds=[{}..{}]",
                cursor, lower, upper
            );
            let instr = &code[upper as usize];
            if matches!(instr, Bytecode::Branch(..)) {
                eprintln!("[reconstructor] block {} ends with Branch at pc {}", cursor, upper);
            }
            // quick scan for mid-block Branch/IfThenElse occurrences
            let mut local_mid_branches: Vec<CodeOffset> = vec![];
            let mut local_ifs: Vec<CodeOffset> = vec![];
            for pc in lower..=upper {
                match &code[pc as usize] {
                    Bytecode::Branch(..) if pc != upper => local_mid_branches.push(pc),
                    Bytecode::Call(_, _, crate::stackless_bytecode::Operation::IfThenElse, _, _) => local_ifs.push(pc),
                    _ => {}
                }
            }
            if !local_mid_branches.is_empty() {
                eprintln!("[reconstructor] block {} mid-branches at pcs {:?}", cursor, local_mid_branches);
            }
            if !local_ifs.is_empty() {
                eprintln!("[reconstructor] block {} has IfThenElse ops at pcs {:?}", cursor, local_ifs);
            }
            // Intra-block branch detection: if there's a Branch inside the block (not necessarily at `upper`),
            // split around it and structure an IfThenElse.
            if !matches!(instr, Bytecode::Branch(..)) {
                let mut mid_branch_pc: Option<CodeOffset> = None;
                for pc in lower..=upper {
                    if matches!(code[pc as usize], Bytecode::Branch(..)) {
                        mid_branch_pc = Some(pc);
                        break;
                    }
                }
                if let Some(cond_at) = mid_branch_pc {
                    eprintln!("[reconstructor] considering mid-block Branch at pc {} in block {}", cond_at, cursor);
                    if cond_at < upper {
                        if let Bytecode::Branch(_, tlabel, elabel, _cond) = &code[cond_at as usize] {
                            if let (Some(then_block), Some(else_block)) = (
                                resolve_label_block(code, fwd_cfg, pc_to_block_cache, *tlabel),
                                resolve_label_block(code, fwd_cfg, pc_to_block_cache, *elabel),
                            ) {
                                // Determine merge via IPD of the current block; fallback to reachability heuristic
                                let mut merge_block = StacklessControlFlowGraph::find_immediate_post_dominator(back_cfg, cursor);
                                eprintln!(
                                    "[reconstructor] mid-block IPD for block {} = {:?}",
                                    cursor, merge_block
                                );
                                if merge_block.is_none() {
                                    if can_reach(fwd_cfg, then_block, else_block) {
                                        merge_block = Some(else_block);
                                    } else if can_reach(fwd_cfg, else_block, then_block) {
                                        merge_block = Some(then_block);
                                    }
                                }
                                if let Some(merge_block) = merge_block {
                                    eprintln!(
                                        "[reconstructor] structuring mid-block IfThenElse at pc={} merge={} then={} else={}",
                                        cond_at, merge_block, then_block, else_block
                                    );

                                    // Emit pre-branch straight-line part, if any. Avoid emitting label-only when appropriate.
                                    if lower < cond_at {
                                        let pre_lower = lower;
                                        let mut pre_upper = cond_at - 1;
                                        // Trim jump-to-merge at end of pre region if accurately jumping to merge.
                                        if let Some(spc) = StacklessControlFlowGraph::block_start_pc(fwd_cfg, merge_block) {
                                            if let Bytecode::Jump(_, jlabel) = &code[pre_upper as usize] {
                                                if let Some(&jpc) = labels.get(jlabel) {
                                                    if jpc == spc && pre_upper > pre_lower {
                                                        pre_upper -= 1;
                                                    }
                                                }
                                            }
                                        }
                                        let is_label_only = pre_lower == pre_upper && matches!(code[pre_lower as usize], Bytecode::Label(..));
                                        let single_pred = back_cfg.successors(cursor).len() == 1;
                                        if !(is_label_only && single_pred && !seq.is_empty()) {
                                            seq.push(StructuredBlock::Basic { lower: pre_lower, upper: pre_upper });
                                        }
                                    }

                                    // Build branches up to merge
                                    let then_struct = reconstruct_region(
                                        code,
                                        fwd_cfg,
                                        back_cfg,
                                        pc_to_block_cache,
                                        visited,
                                        then_block,
                                        Some(merge_block),
                                    );
                                    let else_struct = if else_block == merge_block {
                                        None
                                    } else {
                                        reconstruct_region(
                                            code,
                                            fwd_cfg,
                                            back_cfg,
                                            pc_to_block_cache,
                                            visited,
                                            else_block,
                                            Some(merge_block),
                                        )
                                    };

                                    eprintln!(
                                        "[reconstructor] EMIT mid-block IfThenElse cond_at={} then={} else={} merge={}",
                                        cond_at, then_block, else_block, merge_block
                                    );
                                    seq.push(StructuredBlock::IfThenElse {
                                        cond_at,
                                        then_branch: Box::new(then_struct.unwrap_or(StructuredBlock::Seq(vec![]))),
                                        else_branch: else_struct.map(|b| Box::new(b)),
                                    });

                                    // Continue from merge point within the same region
                                    if let Some(rest) = reconstruct_region(
                                        code,
                                        fwd_cfg,
                                        back_cfg,
                                        pc_to_block_cache,
                                        visited,
                                        merge_block,
                                        stop_block,
                                    ) {
                                        match rest {
                                            StructuredBlock::Seq(v) => seq.extend(v),
                                            other => seq.push(other),
                                        }
                                    }
                                    break;
                                }
                                eprintln!("[reconstructor] mid-block structuring skipped: no merge found");
                            }
                        }
                    }
                }
            }
            if let Bytecode::Branch(_, tlabel, elabel, _cond) = instr {
                // Resolve branch targets safely
                let then_block = match resolve_label_block(code, fwd_cfg, pc_to_block_cache, *tlabel) {
                    Some(b) => b,
                    None => {
                        warn!("CFG reconstruct: failed to resolve then label; emitting Basic");
                        // Fallback to basic emission below
                        // Force path to default block handling by setting a non-Branch tag
                        // but easier: skip structuring by doing nothing here
                        // fallthrough to default below by using a separate scope
                        // To do so, we set a flag
                        // handled by not entering this branch
                        // We cannot mutate instr; so use else path
                        // Instead, emit as Basic now
                        let mut trimmed_upper = upper;
                        if let Some(spc) = stop_pc {
                            if trimmed_upper >= lower {
                                if let Bytecode::Jump(_, jlabel) = &code[trimmed_upper as usize] {
                                    if let Some(&jpc) = labels.get(jlabel) {
                                        if jpc == spc && trimmed_upper > lower {
                                            trimmed_upper -= 1;
                                        }
                                    }
                                }
                            }
                        }
                        let is_label_only = lower == trimmed_upper && matches!(code[lower as usize], Bytecode::Label(..));
                        let single_pred = back_cfg.successors(cursor).len() == 1;
                        if !(is_label_only && single_pred && !seq.is_empty()) {
                            seq.push(StructuredBlock::Basic { lower, upper: trimmed_upper });
                        }
                        if let Some(next) = prefer_fallthrough_successor(fwd_cfg, cursor) {
                            cursor = next;
                            continue;
                        }
                        break;
                    }
                };
                let else_block = match resolve_label_block(code, fwd_cfg, pc_to_block_cache, *elabel) {
                    Some(b) => b,
                    None => {
                        warn!("CFG reconstruct: failed to resolve else label; emitting Basic");
                        let mut trimmed_upper = upper;
                        if let Some(spc) = stop_pc {
                            if trimmed_upper >= lower {
                                if let Bytecode::Jump(_, jlabel) = &code[trimmed_upper as usize] {
                                    if let Some(&jpc) = labels.get(jlabel) {
                                        if jpc == spc && trimmed_upper > lower {
                                            trimmed_upper -= 1;
                                        }
                                    }
                                }
                            }
                        }
                        let is_label_only = lower == trimmed_upper && matches!(code[lower as usize], Bytecode::Label(..));
                        let single_pred = back_cfg.successors(cursor).len() == 1;
                        if !(is_label_only && !single_pred) {
                            seq.push(StructuredBlock::Basic { lower, upper: trimmed_upper });
                        }
                        if let Some(next) = prefer_fallthrough_successor(fwd_cfg, cursor) {
                            cursor = next;
                            continue;
                        }
                        break;
                    }
                };

                // Compute merge via immediate postdominator
                // Try IPD first
                let mut merge_block = StacklessControlFlowGraph::find_immediate_post_dominator(back_cfg, cursor);
                // Heuristic fallback: if no IPD, use reachability between branches
                if merge_block.is_none() {
                    if can_reach(fwd_cfg, then_block, else_block) {
                        merge_block = Some(else_block);
                    } else if can_reach(fwd_cfg, else_block, then_block) {
                        merge_block = Some(then_block);
                    }
                }
                if let Some(merge_block) = merge_block {
                    eprintln!(
                        "[reconstructor] structuring IfThenElse at pc={} merge={} then={} else={}",
                        upper, merge_block, then_block, else_block
                    );
                    // Pre-branch part inside current block, if any (avoid label-only)
                    if lower < upper {
                        let pre_lower = lower;
                        let mut pre_upper = upper - 1;
                        // Trim jump-to-merge if present and accurate
                        if let Some(spc) = StacklessControlFlowGraph::block_start_pc(fwd_cfg, merge_block) {
                            if let Bytecode::Jump(_, jlabel) = &code[pre_upper as usize] {
                                if let Some(&jpc) = labels.get(jlabel) {
                                    if jpc == spc && pre_upper > pre_lower {
                                        pre_upper -= 1;
                                    }
                                }
                            }
                        }
                        let is_label_only = pre_lower == pre_upper && matches!(code[pre_lower as usize], Bytecode::Label(..));
                        let single_pred = back_cfg.successors(cursor).len() == 1;
                        if !(is_label_only && single_pred && !seq.is_empty()) {
                            seq.push(StructuredBlock::Basic { lower: pre_lower, upper: pre_upper });
                        }
                    }

                    // Build branches up to merge
                    let then_struct = reconstruct_region(
                        code,
                        fwd_cfg,
                        back_cfg,
                        pc_to_block_cache,
                        visited,
                        then_block,
                        Some(merge_block),
                    );
                    let else_struct = if else_block == merge_block {
                        None
                    } else {
                        reconstruct_region(
                            code,
                            fwd_cfg,
                            back_cfg,
                            pc_to_block_cache,
                            visited,
                            else_block,
                            Some(merge_block),
                        )
                    };

                        // Assert branch at cond_at (defensive)
                        match &code[upper as usize] {
                            Bytecode::Branch(..) => {}
                            _ => {
                                warn!("CFG reconstruct: expected Branch at block end pc={}, falling back to Basic", upper);
                                let mut trimmed_upper = upper;
                                if let Some(spc) = stop_pc {
                                    if trimmed_upper >= lower {
                                        if let Bytecode::Jump(_, jlabel) = &code[trimmed_upper as usize] {
                                            if let Some(&jpc) = labels.get(jlabel) {
                                                if jpc == spc && trimmed_upper > lower {
                                                    trimmed_upper -= 1;
                                                }
                                            }
                                        }
                                    }
                                }
                                let is_label_only = lower == trimmed_upper && matches!(code[lower as usize], Bytecode::Label(..));
                                let single_pred = back_cfg.successors(cursor).len() == 1;
                                if !(is_label_only && single_pred && !seq.is_empty()) {
                                    seq.push(StructuredBlock::Basic { lower, upper: trimmed_upper });
                                }
                                if let Some(next) = prefer_fallthrough_successor(fwd_cfg, cursor) {
                                    cursor = next;
                                    continue;
                                }
                                break;
                            }
                        }

                        seq.push(StructuredBlock::IfThenElse {
                            cond_at: upper,
                            then_branch: Box::new(then_struct.unwrap_or(StructuredBlock::Seq(vec![]))),
                            else_branch: else_struct.map(|b| Box::new(b)),
                        });

                        // Recurse from merge to continue the region, letting caller own the merge content
                        if let Some(rest) = reconstruct_region(
                            code,
                            fwd_cfg,
                            back_cfg,
                            pc_to_block_cache,
                            visited,
                            merge_block,
                            stop_block,
                        ) {
                            match rest {
                                StructuredBlock::Seq(v) => seq.extend(v),
                                other => seq.push(other),
                            }
                        }
                        break;
                } else {
                    debug!("CFG reconstruct: no IPD merge found; emitting Basic");
                }
                // Fallback: emit as Basic and advance
                let mut trimmed_upper = upper;
                if let Some(spc) = stop_pc {
                    if trimmed_upper >= lower {
                        if let Bytecode::Jump(_, jlabel) = &code[trimmed_upper as usize] {
                            if let Some(&jpc) = labels.get(jlabel) {
                                if jpc == spc && trimmed_upper > lower {
                                    trimmed_upper -= 1;
                                }
                            }
                        }
                    }
                }
                let is_label_only = lower == trimmed_upper && matches!(code[lower as usize], Bytecode::Label(..));
                let single_pred = back_cfg.successors(cursor).len() == 1;
                if !(is_label_only && single_pred && !seq.is_empty()) {
                    seq.push(StructuredBlock::Basic { lower, upper: trimmed_upper });
                }
                if let Some(next) = prefer_fallthrough_successor(fwd_cfg, cursor) {
                    cursor = next;
                    continue;
                }
                break;
            }

            // Default: just a basic block (with safer trimming and label-only preservation rules)
            if let BlockContent::Basic { lower, mut upper } = fwd_cfg.content(cursor) {
                if let Some(spc) = stop_pc {
                    if upper >= *lower {
                        if let Bytecode::Jump(_, jlabel) = &code[upper as usize] {
                            if let Some(&jpc) = labels.get(jlabel) {
                                if jpc == spc && upper > *lower {
                                    upper -= 1;
                                }
                            }
                        }
                    }
                }
                let is_label_only = *lower == upper && matches!(code[*lower as usize], Bytecode::Label(..));
                let single_pred = back_cfg.successors(cursor).len() == 1;
                if !(is_label_only && single_pred && !seq.is_empty()) {
                    seq.push(StructuredBlock::Basic { lower: *lower, upper });
                }
            }

            if let Some(next) = prefer_fallthrough_successor(fwd_cfg, cursor) {
                if Some(next) == stop_block {
                    break;
                }
                if local.contains(&next) {
                    break;
                }
                cursor = next;
            } else {
                break;
            }
        }

        for b in &local {
            visited.insert(*b);
        }

        if seq.is_empty() {
            None
        } else if seq.len() == 1 {
            Some(seq.remove(0))
        } else {
            Some(StructuredBlock::Seq(seq))
        }
    }

    let mut result: Vec<StructuredBlock> = Vec::new();
    let entry = fwd_cfg.entry_block();
    if let Some(s) = reconstruct_region(
        code,
        &fwd_cfg,
        &back_cfg,
        &mut pc_to_block_cache,
        &mut visited,
        entry,
        None,
    ) {
        match s {
            StructuredBlock::Seq(v) => result.extend(v),
            other => result.push(other),
        }
    }

    // Conservative fallback: if nothing was reconstructed (e.g., all were label-only blocks),
    // emit a flat sequence of all basic blocks to avoid empty bodies downstream.
    if result.is_empty() {
        let mut flat: Vec<StructuredBlock> = Vec::new();
        for b in fwd_cfg.blocks() {
            if let BlockContent::Basic { lower, upper } = fwd_cfg.content(b) {
                flat.push(StructuredBlock::Basic { lower: *lower, upper: *upper });
            }
        }
        if flat.len() <= 1 {
            flat
        } else {
            vec![StructuredBlock::Seq(flat)]
        }
    } else {
        result
    }
}
