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
//! - Tracks variables to assigns and calls with a single destination var
//!   (call return value assigned).
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
    graph::Graph,
    livevar_analysis::LiveVarAnnotation,
    stackless_bytecode::{AttrId, Bytecode, Label, Operation},
    stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph},
};
use move_model::model::FunctionEnv;
use std::collections::{BTreeMap, BTreeSet};
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

    fn has_loops(&self, code: &[Bytecode]) -> bool {
        if code.is_empty() {
            return false;
        }

        let forward_cfg = StacklessControlFlowGraph::new_forward(code);
        let entry = forward_cfg.entry_block();
        let nodes = forward_cfg.blocks();

        let edges: Vec<(BlockId, BlockId)> = nodes
            .iter()
            .flat_map(|x| forward_cfg.successors(*x).iter().map(|y| (*x, *y)))
            .collect();

        let graph = Graph::new(entry, nodes, edges);
        match graph.compute_reducible() {
            Some(natural_loops) => !natural_loops.is_empty(),
            // None implies irreducible or malformed -> reject
            None => true,
        }
    }

    // Dominator-based merge detection for a branch at pc.
    // Returns the merge label if we can determine a valid merge pattern.
    //
    // Recall the immediate postdominator of the branch corresponds to the
    // structural join. For SSA-style placement of `if_then_else` (phi) per
    // variable, we compute the dominance frontier of each definition and place
    // merges at those DF nodes. This function currently finds the structural
    // join (later phases can refine per-var merge placement using DF).
    fn find_merge_by_dominators(
        &self,
        code: &[Bytecode],
        back_cfg: &StacklessControlFlowGraph,
        branch_pc: usize,
    ) -> Option<Label> {
        let labels = Bytecode::label_offsets(code);
        let branch_block = StacklessControlFlowGraph::pc_to_block(back_cfg, branch_pc as u16)?;
        // Compute merge block as immediate post-dominator of the branch block using
        // reversed-graph dominator analysis (postdominators of the original graph).
        let merge_block =
            StacklessControlFlowGraph::find_immediate_post_dominator(back_cfg, branch_block)?;
        let merge_pc = StacklessControlFlowGraph::block_start_pc(back_cfg, merge_block)?;

        // Find the label that corresponds to merge_pc
        labels
            .iter()
            .find(|(_, &pc)| pc == merge_pc)
            .map(|(label, _)| *label)
    }

    fn is_side_effecting_op(op: &Operation) -> bool {
        use Operation::*;
        matches!(
            op,
            MoveTo(..)
                | MoveFrom(..)
                | BorrowGlobal(..)
                | GetGlobal(..)
                | WriteRef
                | Havoc(..)
                | Stop
                | Uninit
                | Destroy
                | EmitEvent
                | EventStoreDiverge
        )
    }

    // Helper function to scan a block for simple assignments
    // Returns all assigned variables and their sources
    fn block_permitted(
        &self,
        orig_code: &[Bytecode],
        start_pc: usize,
        end_pc: usize,
    ) -> Option<BTreeMap<usize, usize>> {
        let mut scan_pc = start_pc;
        let mut last_assign_per_var: BTreeMap<usize, usize> = BTreeMap::new();
        let mut simple_block = true;

        while scan_pc < orig_code.len() && scan_pc < end_pc {
            match &orig_code[scan_pc] {
                Bytecode::Assign(_, dst, src, _) => {
                    last_assign_per_var.insert(*dst, *src);
                }
                Bytecode::Call(_, dests, op, _srcs, _aa) => {
                    // Allow single-destination calls (assignments) and TraceLocal (debug instrumentation)
                    if dests.len() == 1 && !Self::is_side_effecting_op(op) {
                        let var = dests[0];
                        last_assign_per_var.insert(var, var);
                    } else if matches!(op, Operation::TraceLocal(_)) {
                        // TraceLocal, safe to ignore
                    } else {
                        simple_block = false;
                        break;
                    }
                }
                Bytecode::Jump(..) => {
                    // Expected: blocks should jump to merge point at end of block
                    if scan_pc + 1 < end_pc && scan_pc + 1 < orig_code.len() {
                        // Jump not at the end of block (?) -> reject
                        simple_block = false;
                        break;
                    }
                }

                // Accepted insns
                Bytecode::Nop(..)
                | Bytecode::Load(..)
                | Bytecode::SaveMem(..)
                | Bytecode::Prop(..) => {}

                // Rejected insns
                Bytecode::Label(..) => {
                    if scan_pc != start_pc {
                        // Labels in the middle of blocks not supported
                        simple_block = false;
                        break;
                    }
                }
                Bytecode::Branch(..) => {
                    // Nested branches not supported yet
                    simple_block = false;
                    break;
                }
                Bytecode::Ret(..) | Bytecode::Abort(..) => {
                    // Early returns/aborts change control flow
                    simple_block = false;
                    break;
                }
                Bytecode::VariantSwitch(..) => {
                    // Complex control flow rejected
                    simple_block = false;
                    break;
                }
            }
            scan_pc += 1;
        }

        let pattern_ok = simple_block && !last_assign_per_var.is_empty();
        if pattern_ok {
            return Some(last_assign_per_var);
        }

        None
    }

    // Build conditional insert using postdominator analysis results
    // Handles both if-then (fallthrough) and if-then-else patterns uniformly
    fn build_conditional_insert(
        &self,
        code: &[Bytecode],
        then_label: Label,
        else_label: Label,
        merge_label: Label,
        cond_idx: usize,
        src_attr: AttrId,
        current_val: &BTreeMap<usize, usize>,
        builder: &mut FunctionDataBuilder,
        liveness: Option<&LiveVarAnnotation>,
    ) -> Option<(Label, Vec<Insertion>)> {
        let labels = Bytecode::label_offsets(code);
        let then_pc = *labels.get(&then_label)? as usize;
        let else_pc = *labels.get(&else_label)? as usize;
        let merge_pc = *labels.get(&merge_label)? as usize;

        // Scan the then-block: from then_pc to else_pc
        let then_assignments = self.block_permitted(code, then_pc, else_pc)?;

        // Scan the else-block: from else_pc to merge_pc
        // If else_pc == merge_pc, there's no else block (pure fallthrough)
        let else_assignments = if else_pc < merge_pc {
            self.block_permitted(code, else_pc, merge_pc)
        } else {
            None
        };

        let mut insertions = Vec::new();

        // Get live variables at the merge point to filter unnecessary insertions
        let live_vars_at_merge = if let Some(liveness) = liveness {
            liveness
                .get_live_var_info_at(merge_pc as u16)
                .map(|info| &info.after)
        } else {
            None
        };

        // Collect all variables assigned in either then-block or else-block
        let mut all_assigned_vars: BTreeSet<usize> = BTreeSet::new();
        all_assigned_vars.extend(then_assignments.keys());
        if let Some(else_map) = &else_assignments {
            all_assigned_vars.extend(else_map.keys());
        }

        // Create insertions for all live assigned variables
        for &var in &all_assigned_vars {
            // Skip if we have liveness info and this variable is not live at merge
            if live_vars_at_merge.map_or(false, |live_vars| !live_vars.contains(&var)) {
                continue;
            }

            let var_ty = builder.get_local_type(var);
            let then_src_opt = then_assignments.get(&var);
            let else_src_opt = else_assignments.as_ref().and_then(|m| m.get(&var));

            let mut fresh_vars_in_then = BTreeMap::new();
            let mut fresh_vars_in_else = BTreeMap::new();

            let (then_var, else_var) = match (then_src_opt, else_src_opt) {
                (Some(&then_src), Some(&else_src)) => {
                    // Both blocks assign: create fresh variables for both
                    let fresh_then_var = builder.new_temp(var_ty.clone());
                    let fresh_else_var = builder.new_temp(var_ty);
                    fresh_vars_in_then.insert(var, fresh_then_var);
                    fresh_vars_in_else.insert(var, fresh_else_var);
                    (then_src, else_src)
                }
                (Some(&then_src), None) => {
                    // Only then block assigns: fresh then var, fallthrough else var
                    let fresh_then_var = builder.new_temp(var_ty);
                    fresh_vars_in_then.insert(var, fresh_then_var);
                    let fallthrough = *current_val.get(&var).unwrap_or(&var);
                    (then_src, fallthrough)
                }
                (None, Some(&else_src)) => {
                    // Only else block assigns: fallthrough then var, fresh else var
                    let fresh_else_var = builder.new_temp(var_ty);
                    fresh_vars_in_else.insert(var, fresh_else_var);
                    let fallthrough = *current_val.get(&var).unwrap_or(&var);
                    (fallthrough, else_src)
                }
                (None, None) => {
                    // Neither block assigns (shouldn't happen due to collection logic)
                    continue;
                }
            };

            let insertion = Insertion {
                dest_var: var,
                cond: cond_idx,
                then_var,
                src_attr,
                else_var,
                fresh_vars_in_then,
                fresh_vars_in_else,
            };

            insertions.push(insertion);
        }

        if insertions.is_empty() {
            None
        } else {
            Some((merge_label, insertions))
        }
    }
}

#[derive(Clone, Debug)]
struct Insertion {
    src_attr: AttrId,
    dest_var: usize,
    cond: usize,
    then_var: usize,
    else_var: usize,
    fresh_vars_in_then: BTreeMap<usize, usize>,
    fresh_vars_in_else: BTreeMap<usize, usize>,
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
        if !targets.prover_options().enable_conditional_merge_insertion
            && !self.debug
            && !(targets.is_pure_fun(&func_env.get_qualified_id())
                && !targets.func_abort_check_mode())
        {
            return data; // Skip if option not set, but keep for pure
        }

        let mut builder = FunctionDataBuilder::new(func_env, data);
        let orig_code = builder.data.code.clone();
        if orig_code.is_empty() {
            return builder.data;
        }

        let liveness = builder.data.annotations.get::<LiveVarAnnotation>().cloned();

        let mut current_val: BTreeMap<usize, usize> = (0..builder.data.local_types.len())
            .map(|i| (i, i))
            .collect();
        // pending inserts track where to insert a if_then_else(...)'s after a Label
        let mut pending_inserts: BTreeMap<Label, Vec<Insertion>> = BTreeMap::new();
        let back_cfg = Some(StacklessControlFlowGraph::new_backward(&orig_code, false));

        // Skip functions with loops
        if self.has_loops(&orig_code) {
            return builder.data;
        }

        let mut active_fresh_vars: BTreeMap<usize, usize> = BTreeMap::new();
        let mut label_to_fresh_vars: BTreeMap<Label, BTreeMap<usize, usize>> = BTreeMap::new();

        let mut pc = 0; // TODO(@rvantonder): can we do this pass without pc?
        for bc in mem::take(&mut builder.data.code) {
            match bc {
                // Check labels for inserting if_then_else(...)
                Bytecode::Label(attr_id, label) => {
                    builder.emit(Bytecode::Label(attr_id, label));

                    if let Some(fresh_vars_map) = label_to_fresh_vars.get(&label) {
                        active_fresh_vars = fresh_vars_map.clone();
                    } else {
                        active_fresh_vars.clear();
                    }

                    if let Some(list) = pending_inserts.remove(&label) {
                        for ins in list {
                            // Set location/debug context from the originating branch instruction
                            builder.set_loc_from_attr(ins.src_attr);
                            // Allocate a fresh temp of same type as `var`
                            let var_ty = builder.get_local_type(ins.dest_var);
                            let new_temp = builder.new_temp(var_ty);

                            let fresh_then_var = ins
                                .fresh_vars_in_then
                                .get(&ins.dest_var)
                                .unwrap_or(&ins.then_var);

                            let fresh_else_var = ins
                                .fresh_vars_in_else
                                .get(&ins.dest_var)
                                .unwrap_or(&ins.else_var);

                            builder.set_next_debug_comment(format!(
                                "conditional_merge_insertion: t{} := if_then_else(t{}, t{}, t{})",
                                new_temp, ins.cond, fresh_then_var, fresh_else_var
                            ));
                            builder.emit_with(|id| {
                                Bytecode::Call(
                                    id,
                                    vec![new_temp],
                                    Operation::IfThenElse,
                                    vec![ins.cond, *fresh_then_var, *fresh_else_var],
                                    None,
                                )
                            });

                            current_val.insert(ins.dest_var, new_temp);
                        }
                    }
                }
                Bytecode::Branch(attr, then_label, else_label, cond_idx) => {
                    let merge_label =
                        self.find_merge_by_dominators(&orig_code, back_cfg.as_ref().unwrap(), pc);

                    if merge_label.is_none() {
                        // Note: early returns in conditional branches have no merge label
                        builder.emit(Bytecode::Branch(attr, then_label, else_label, cond_idx));
                        continue;
                    }
                    // Invariant: merge_label is Some
                    let merge_label = merge_label.unwrap();
                    if let Some((insertion_label, insertions)) = self.build_conditional_insert(
                        &orig_code,
                        then_label,
                        else_label,
                        merge_label,
                        cond_idx,
                        attr,
                        &current_val,
                        &mut builder,
                        liveness.as_ref(),
                    ) {
                        // Collect fresh variables for then-block from all insertions
                        let mut fresh_vars_for_then_block = BTreeMap::new();
                        let mut fresh_vars_for_else_block = BTreeMap::new();

                        for insertion in &insertions {
                            // Collect then-block fresh vars
                            for (&var, &fresh_var) in &insertion.fresh_vars_in_then {
                                fresh_vars_for_then_block.insert(var, fresh_var);
                            }
                            // Collect else-block fresh vars
                            for (&var, &fresh_var) in &insertion.fresh_vars_in_else {
                                fresh_vars_for_else_block.insert(var, fresh_var);
                            }
                        }

                        if !fresh_vars_for_then_block.is_empty() {
                            label_to_fresh_vars.insert(then_label, fresh_vars_for_then_block);
                        }
                        if !fresh_vars_for_else_block.is_empty() {
                            label_to_fresh_vars.insert(else_label, fresh_vars_for_else_block);
                        }

                        pending_inserts
                            .entry(insertion_label)
                            .or_default()
                            .extend(insertions);
                    }
                    builder.emit(Bytecode::Branch(attr, then_label, else_label, cond_idx))
                }
                Bytecode::Assign(attr, original_dst, src, kind) => {
                    let fresh_dst = active_fresh_vars
                        .get(&original_dst)
                        .copied()
                        .unwrap_or(original_dst);
                    // Remap source operand through current_val to use SSA variable
                    let remapped_src = current_val.get(&src).copied().unwrap_or(src);
                    current_val.insert(original_dst, remapped_src); // Track latest rhs value of original dst
                    builder.emit(Bytecode::Assign(attr, fresh_dst, remapped_src, kind))
                }
                Bytecode::Call(attr, dests, op, srcs, abort) if dests.len() == 1 => {
                    let original_dest = dests[0];
                    let actual_dest = active_fresh_vars
                        .get(&original_dest)
                        .copied()
                        .unwrap_or(original_dest);
                    // Remap source operands through current_val to use SSA variables
                    let remapped_srcs: Vec<usize> = srcs
                        .iter()
                        .map(|&s| current_val.get(&s).copied().unwrap_or(s))
                        .collect();
                    current_val.insert(original_dest, actual_dest);
                    builder.emit(Bytecode::Call(
                        attr,
                        vec![actual_dest],
                        op,
                        remapped_srcs,
                        abort,
                    ))
                }
                Bytecode::Call(attr, dests, op, srcs, abort) if dests.is_empty() => {
                    // Handle calls with no destinations (e.g., TraceReturn, TraceLocal, TraceAbort)
                    // Remap source operands through current_val to use SSA variables
                    let remapped_srcs: Vec<usize> = srcs
                        .iter()
                        .map(|&s| current_val.get(&s).copied().unwrap_or(s))
                        .collect();
                    builder.emit(Bytecode::Call(attr, dests, op, remapped_srcs, abort))
                }
                Bytecode::Ret(attr, srcs) => {
                    let remapped_srcs = srcs
                        .iter()
                        .map(|&s| current_val.get(&s).copied().unwrap_or(s))
                        .collect();
                    builder.emit(Bytecode::Ret(attr, remapped_srcs))
                }
                Bytecode::Abort(attr, src) => {
                    let remapped_src = current_val.get(&src).copied().unwrap_or(src);
                    builder.emit(Bytecode::Abort(attr, remapped_src))
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
