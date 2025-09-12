// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Inserts `if_then_else` at merge points for simple consecutive if-statements
//! while keeping original control flow intact. This is intended to make merge
//! semantics explicit for later verification/optimization passes.
//!
//! Supported pattern per if-block:
//! - Bytecode::Branch(then_label, else_label, cond)
//! - then_label block ends with Jump to else_label
//! - else_label is the merge label (fallthrough path)
//! - Simplifying assumption: pick the last Assign in the then block as
//!   the then-value producer for the merged variable, and the last assignment
//!   to the same variable before the Branch as the else-value.
//!
//! The pass inserts at the merge label (right after the Label):
//!   t_new := if_then_else(cond, then_src, else_src)
//!   var   := t_new
//!
//! Branch-local assignments are left in place (they may be dead after merge
//! and can be cleaned up by later passes).

use crate::{
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    graph::{DomRelation, Graph},
    stackless_bytecode::{AssignKind, AttrId, Bytecode, Label, Operation},
    stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph},
};
use move_compiler::shared::known_attributes::AttributeKind_;
use move_model::model::FunctionEnv;
use std::collections::BTreeMap;
use std::mem;

pub struct ConditionalMergeInsertionProcessor {
    debug: bool,
}

impl ConditionalMergeInsertionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self { debug: false })
    }

    #[allow(dead_code)]
    pub fn new_with_debug() -> Box<Self> {
        Box::new(Self { debug: true })
    }

    // Dominator-based merge detection for a branch at pc.
    // Returns (cond_temp, then_start_pc, merge_block_start_pc) if we can determine a merge.
    //
    // Recall the immediate postdominator of the branch corresponds to the
    // structural join. For SSA-style placement of `if_then_else` (phi) per
    // variable, we compute the dominance frontier of each definition and place
    // merges at those DF nodes. This function currently finds the structural
    // join (later phases can refine per-var merge placement using DF).
    fn find_merge_by_dominators(
        code: &[Bytecode],
        back_cfg: &StacklessControlFlowGraph,
        branch_pc: usize,
    ) -> Option<(usize, usize, usize)> {
        let (then_label, cond) = match &code[branch_pc] {
            Bytecode::Branch(_, tl, _el, cond) => (tl, *cond),
            _ => return None,
        };

        let labels = Bytecode::label_offsets(code);
        let then_pc = *labels.get(then_label)?;
        let branch_block = Self::pc_to_block(back_cfg, branch_pc as u16)?;

        // Compute merge block as immediate post-dominator of the branch block using
        // reversed-graph dominator analysis (postdominators of the original graph).
        let merge_block = Self::find_immediate_post_dominator(back_cfg, branch_block)?;
        let merge_pc = Self::block_start_pc(back_cfg, merge_block)?;

        Some((cond, then_pc as usize, merge_pc as usize))
    }

    fn block_start_pc(cfg: &StacklessControlFlowGraph, block: BlockId) -> Option<u16> {
        match cfg.content(block) {
            BlockContent::Basic { lower, .. } => Some(*lower),
            BlockContent::Dummy => None,
        }
    }

    fn pc_to_block(cfg: &StacklessControlFlowGraph, pc: u16) -> Option<BlockId> {
        for b in cfg.blocks() {
            match cfg.content(b) {
                BlockContent::Basic { lower, upper } => {
                    if *lower <= pc && pc <= *upper {
                        return Some(b);
                    }
                }
                BlockContent::Dummy => {}
            }
        }
        None
    }

    fn find_immediate_post_dominator(
        back_cfg: &StacklessControlFlowGraph,
        branch_block: BlockId,
    ) -> Option<BlockId> {
        // Build reversed graph and compute dominators (postdominators of original CFG)
        let entry = back_cfg.entry_block();
        let nodes = back_cfg.blocks();
        let edges: Vec<(BlockId, BlockId)> = nodes
            .iter()
            .flat_map(|x| {
                back_cfg
                    .successors(*x)
                    .iter()
                    .map(|y| (*x, *y))
                    .collect::<Vec<_>>()
            })
            .collect();
        let graph = Graph::new(entry, nodes.clone(), edges);
        let dom_rev = DomRelation::new(&graph);

        // Candidates are postdominators of branch_block (including itself and exit)
        let candidates: Vec<BlockId> = nodes
            .into_iter()
            .filter(|b| {
                *b != branch_block
                    && dom_rev.is_reachable(*b)
                    && dom_rev.is_dominated_by(branch_block, *b)
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        // Immediate postdominator is the next node required on any path to exit--
        // i.e., deepest candidate: it should not dominate any other candidate.
        for &c in &candidates {
            let mut dominates_any = false;
            for &o in &candidates {
                if o != c && dom_rev.is_dominated_by(o, c) {
                    // c dominates o in reversed graph => c is above; skip it
                    dominates_any = true;
                    break;
                }
            }
            if !dominates_any {
                return Some(c);
            }
        }
        // Fallback
        candidates.into_iter().next()
    }

    // Validate that the computed merge is the else_label (i.e., if-with-fallthrough),
    // scan the then-block for a simple single-assignment pattern, and if matched,
    // record a pending insertion at the merge label.
    // Returns: (var, then_src, else_src, insertion_label) - None for else_src means use current_val
    fn find_merge_for_fallthrough(
        &self,
        orig_code: &[Bytecode],
        else_label: Label,
        then_start: usize,
        merge_pc: usize,
    ) -> Option<(usize, usize, Option<usize>, Label)> {
        let labels = Bytecode::label_offsets(orig_code);
        let Some(else_pc) = labels.get(&else_label) else {
            return None;
        };
        if merge_pc != *else_pc as usize {
            // This is not a fallthrough pattern, try if-then-else pattern
            return self.find_merge_for_if_then_else(orig_code, else_label, then_start, merge_pc);
        }

        // Scan inside then-block [then_start, merge_pc).
        let mut scan_pc = then_start;
        let mut last_assign_per_var: BTreeMap<usize, usize> = BTreeMap::new();
        let mut last_assigned_var: Option<usize> = None;
        let mut ok_jump_to_else = false;
        let mut saw_uncond_branch = false;
        let mut simple_then = true;
        while scan_pc < orig_code.len() && scan_pc < merge_pc {
            match &orig_code[scan_pc] {
                Bytecode::Assign(_, dst, src, _) => {
                    // Track last assignment to each variable and remember the most recent assignment
                    last_assign_per_var.insert(*dst, *src);
                    last_assigned_var = Some(*dst);
                }
                Bytecode::Call(_, dests, _op, _srcs, _aa) if !dests.is_empty() => {
                    // Track call result as assignment to destination
                    let var = dests[0]; // Dest must exist, i.e., return value of call assigned.
                    last_assign_per_var.insert(var, var);
                    last_assigned_var = Some(var);
                }
                Bytecode::Call(_, _dests, Operation::TraceLocal(_), _srcs, _aa) => {
                    // TODO(rvantondeR): TraceLocals are fine, and so are other debugging ops (which we should add).
                }
                Bytecode::Branch(..) => {
                    simple_then = false; // TODO(rvantonder): reject if nested conditional in then
                    break;
                }
                Bytecode::Label(..) => {
                    if scan_pc != then_start {
                        simple_then = false; // TODO(rvantonder): reject if extra label inside then
                        break;
                    }
                }
                Bytecode::Load(..) => {}
                _ => {
                    // Ultra conservative: reject any other bytecode ops in the block so we don't break things
                    simple_then = false;
                    break;
                }
            }
            if orig_code[scan_pc].is_unconditional_branch() {
                saw_uncond_branch = true;
                if let Bytecode::Jump(_, label) = &orig_code[scan_pc] {
                    ok_jump_to_else = *label == else_label;
                } else {
                    // Punt: this is an unconditional branch that doesn't jump to where we expect.
                    ok_jump_to_else = false;
                }
                break;
            }
            scan_pc += 1;
        }
        if !saw_uncond_branch {
            // Accept implicit fallthrough into merge label.
            ok_jump_to_else = true;
        }

        // Use the last assigned variable (most recent assignment in the then-block)
        let pattern_ok = simple_then && ok_jump_to_else && last_assigned_var.is_some();
        if pattern_ok {
            let var = last_assigned_var.unwrap();
            let then_src = *last_assign_per_var.get(&var).unwrap();
            return Some((var, then_src, None, else_label));
        }
        None
    }

    // Handle if-then-else pattern where both then and else blocks have assignments
    // and both jump to a common merge point (not fallthrough)
    // Returns: (var, then_src, else_src, merge_label) for if-then-else patterns
    fn find_merge_for_if_then_else(
        &self,
        orig_code: &[Bytecode],
        else_label: Label,
        then_start: usize,
        _merge_pc: usize,
    ) -> Option<(usize, usize, Option<usize>, Label)> {
        let labels = Bytecode::label_offsets(orig_code);
        let Some(else_pc) = labels.get(&else_label) else {
            return None;
        };
        let else_start = *else_pc as usize;

        // Find the merge label by following the then-block's exit jump
        let mut merge_label: Option<Label> = None;
        for pc in then_start..else_start {
            if pc < orig_code.len() {
                if let Bytecode::Jump(_, label) = &orig_code[pc] {
                    merge_label = Some(*label);
                    break;
                }
            }
        }

        let Some(merge_label) = merge_label else {
            return None;
        };

        // Scan then-block [then_start, else_start)
        let then_assignment = self.block_permitted(orig_code, then_start, else_start);
        if then_assignment.is_none() {
            return None;
        }

        // For else-block, scan from else_start until we reach the merge label
        let mut else_end = orig_code.len();
        for pc in else_start..orig_code.len() {
            if let Bytecode::Label(_, label) = &orig_code[pc] {
                if *label == merge_label {
                    else_end = pc;
                    break;
                }
            }
        }

        let else_assignment = self.block_permitted(orig_code, else_start, else_end);
        if else_assignment.is_none() {
            return None;
        }

        let (then_var, then_src) = then_assignment.unwrap();
        let (else_var, else_src) = else_assignment.unwrap();

        // Both blocks must assign to the same variable
        if then_var != else_var {
            return None;
        }

        // Return if-then-else pattern with explicit else_src and merge_label
        Some((then_var, then_src, Some(else_src), merge_label))
    }

    // Helper function to scan a block for simple assignments, similar to the logic in find_merge_for_fallthrough
    fn block_permitted(
        &self,
        orig_code: &[Bytecode],
        start_pc: usize,
        end_pc: usize,
    ) -> Option<(usize, usize)> {
        let mut scan_pc = start_pc;
        let mut last_assign_per_var: BTreeMap<usize, usize> = BTreeMap::new();
        let mut last_assigned_var: Option<usize> = None;
        let mut simple_block = true;

        while scan_pc < orig_code.len() && scan_pc < end_pc {
            match &orig_code[scan_pc] {
                Bytecode::Assign(_, dst, src, _) => {
                    last_assign_per_var.insert(*dst, *src);
                    last_assigned_var = Some(*dst);
                }
                Bytecode::Call(_, dests, _op, _srcs, _aa) if !dests.is_empty() => {
                    let var = dests[0];
                    last_assign_per_var.insert(var, var);
                    last_assigned_var = Some(var);
                }
                Bytecode::Branch(..) => {
                    simple_block = false;
                    break;
                }
                Bytecode::Label(..) => {
                    if scan_pc != start_pc {
                        simple_block = false;
                        break;
                    }
                }
                Bytecode::Jump(..) => {
                    // Expected: blocks should jump to merge point
                }
                Bytecode::Load(..) => {}
                _ => {
                    // Ultra conservative: reject any other bytecode ops in the block so we don't break things
                    simple_block = false;
                    break;
                }
            }
            scan_pc += 1;
        }

        let pattern_ok = simple_block && last_assigned_var.is_some();
        if pattern_ok {
            let var = last_assigned_var.unwrap();
            let src = *last_assign_per_var.get(&var).unwrap();
            return Some((var, src));
        }

        None
    }
}

#[derive(Clone, Debug)]
struct Insertion {
    var: usize,
    cond: usize,
    then_src: usize,
    // attribute to inherit location/debug context from (taken from Branch)
    src_attr: AttrId,
    // For if-then-else patterns, store the explicit else_src instead of using current_val
    explicit_else_src: Option<usize>,
}

impl FunctionTargetProcessor for ConditionalMergeInsertionProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if targets.is_spec(&func_env.get_qualified_id()) {
            return data; // Do not touch specs
        }
        if func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::SpecOnly)
            .is_some()
        {
            return data; // Do not touch spec_only
        }

        let mut builder = FunctionDataBuilder::new(func_env, data);
        let orig_code = builder.data.code.clone();
        if orig_code.is_empty() {
            return builder.data;
        }

        // XXX(@rvantonder): For simplicity, rejects functions with early returns (no Ret at the end)
        let last_idx = orig_code.len().saturating_sub(1);
        let has_early_ret = orig_code
            .iter()
            .enumerate()
            .any(|(i, bc)| matches!(bc, Bytecode::Ret(..)) && i < last_idx);
        if has_early_ret {
            // Punt: do not transform this function
            return builder.data;
        }
        let mut current_val: BTreeMap<usize, usize> = (0..builder.data.local_types.len())
            .map(|i| (i, i))
            .collect();
        // pending inserts track where to insert a if_then_else(...)'s after a Label
        let mut pending_inserts: BTreeMap<Label, Vec<Insertion>> = BTreeMap::new();
        let back_cfg = Some(StacklessControlFlowGraph::new_backward(&orig_code, false));

        let mut pc = 0; // TODO(@rvantonder): can we do this pass without pc?
        for bc in mem::take(&mut builder.data.code) {
            match bc {
                // Check labels for inserting if_then_else(...)
                Bytecode::Label(attr_id, label) => {
                    builder.emit(Bytecode::Label(attr_id, label));
                    if let Some(list) = pending_inserts.remove(&label) {
                        for ins in list {
                            // Set location/debug context from the originating branch instruction
                            builder.set_loc_from_attr(ins.src_attr);
                            // Allocate a fresh temp of same type as `var`
                            let var_ty = builder.get_local_type(ins.var);
                            let new_temp = builder.new_temp(var_ty);

                            // Use the captured else_src (always available now)
                            let else_src = ins.explicit_else_src.expect("conditional_merge_insertion: explicit_else_src should always be Some here");

                            builder.set_next_debug_comment(format!(
                                "conditional_merge_insertion: t{} := if_then_else(t{}, t{}, t{})",
                                new_temp, ins.cond, ins.then_src, else_src
                            ));
                            builder.emit_with(|id| {
                                Bytecode::Call(
                                    id,
                                    vec![new_temp],
                                    Operation::IfThenElse,
                                    vec![ins.cond, ins.then_src, else_src],
                                    None,
                                )
                            });

                            builder.set_next_debug_comment(format!(
                                "conditional_merge_insertion: merge assign t{} := t{}",
                                ins.var, new_temp
                            ));
                            builder.emit_with(|id| {
                                Bytecode::Assign(id, ins.var, new_temp, AssignKind::Store)
                            });
                            current_val.insert(ins.var, new_temp);
                        }
                    }
                }
                Bytecode::Branch(attr, _then_label, else_label, _cond) => {
                    // Only processes insertion for strict `if (cond) { ... }` with fallthrough merge:
                    // Use dominator-based merge detection to find the merge, then validate
                    // the then-block is simple and contains exactly one write.
                    let dominator =
                        Self::find_merge_by_dominators(&orig_code, back_cfg.as_ref().unwrap(), pc);
                    if let Some((cond_idx, then_start, merge_pc)) = dominator {
                        let merge_point = self.find_merge_for_fallthrough(
                            &orig_code, else_label, then_start, merge_pc,
                        );

                        if let Some((var, then_src, explicit_else_src, insertion_label)) =
                            merge_point
                        {
                            // For fallthrough patterns, capture the current else_src value now
                            let final_else_src = if explicit_else_src.is_some() {
                                explicit_else_src
                            } else {
                                // Fallthrough pattern: use current_val at branch time
                                Some(*current_val.get(&var).unwrap_or(&var))
                            };

                            pending_inserts
                                .entry(insertion_label)
                                .or_default()
                                .push(Insertion {
                                    var,
                                    cond: cond_idx,
                                    then_src,
                                    src_attr: attr,
                                    explicit_else_src: final_else_src,
                                });
                        }
                    }
                    builder.emit(Bytecode::Branch(attr, _then_label, else_label, _cond))
                }
                Bytecode::Assign(attr, dst, src, kind) => {
                    // Track latest value of destination
                    current_val.insert(dst, src);
                    builder.emit(Bytecode::Assign(attr, dst, src, kind))
                }
                Bytecode::Call(attr, dests, op, srcs, abort) if !dests.is_empty() => {
                    // Dest now holds the produced value
                    current_val.insert(dests[0], dests[0]);
                    // Emit original instruction without moving fields (borrowed above)
                    builder.emit(Bytecode::Call(attr, dests.clone(), op, srcs, abort))
                }
                bytecode => builder.emit(bytecode),
            }
            pc += 1;
        }

        builder.data
    }

    fn name(&self) -> String {
        "conditional_merge_insertion".to_string()
    }
}
