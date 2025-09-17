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
    livevar_analysis::LiveVarAnnotation,
    stackless_bytecode::{AssignKind, AttrId, Bytecode, Label, Operation},
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use move_compiler::shared::known_attributes::AttributeKind_;
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

    // Helper function to scan a block for assignments before any nested control flow
    // For nested conditionals, only considers assignments that happen directly in this block
    // Returns all assigned variables and their sources
    fn block_permitted(
        &self,
        orig_code: &[Bytecode],
        start_pc: usize,
        end_pc: usize,
    ) -> Option<BTreeMap<usize, usize>> {
        let mut scan_pc = start_pc;
        let mut last_assign_per_var: BTreeMap<usize, usize> = BTreeMap::new();
        let mut found_nested_control = false;

        while scan_pc < orig_code.len() && scan_pc < end_pc {
            match &orig_code[scan_pc] {
                Bytecode::Assign(_, dst, src, _) => {
                    if !found_nested_control {
                        // Only record assignments before nested control flow
                        last_assign_per_var.insert(*dst, *src);
                    }
                }
                Bytecode::Call(_, dests, _op, _srcs, _aa) if !dests.is_empty() => {
                    if !found_nested_control {
                        // Only record calls before nested control flow
                        let var = dests[0];
                        last_assign_per_var.insert(var, var);
                    }
                }
                Bytecode::Branch(..) => {
                    // Mark that we found nested control flow - stop considering new assignments
                    found_nested_control = true;
                }
                Bytecode::Label(..) => {
                    if scan_pc != start_pc {
                        // We've entered a nested block, stop considering assignments
                        found_nested_control = true;
                    }
                }
                Bytecode::Jump(..) => {
                    // Expected: blocks should jump to merge point
                }
                Bytecode::Load(..) => {}
                _ => {
                    // Other instructions don't affect our analysis
                }
            }
            scan_pc += 1;
        }

        if !last_assign_per_var.is_empty() {
            Some(last_assign_per_var)
        } else {
            None
        }
    }

    // Build conditional insert using postdominator analysis results
    // Handles both if-then (fallthrough) and if-then-else patterns uniformly
    // Now returns multiple insertions for live assigned variables
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
            liveness.get_live_var_info_at(merge_pc as u16)
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
            if let Some(live_vars) = live_vars_at_merge {
                if !live_vars.contains(&var) {
                    continue;
                }
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

        // Get liveness annotation if available (clone to avoid borrowing issues)
        let liveness = builder.data.annotations.get::<LiveVarAnnotation>().cloned();

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

        let mut active_fresh_vars: BTreeMap<usize, usize> = BTreeMap::new();
        let mut label_to_fresh_vars: BTreeMap<Label, BTreeMap<usize, usize>> = BTreeMap::new();

        // Find all conditionals first
        let conditionals = self.find_all_conditionals(&orig_code, back_cfg.as_ref().unwrap());


        // Process all conditionals to collect insertions
        for conditional in conditionals {
            if let Some((insertion_label, insertions)) = self.build_conditional_insert(
                &orig_code,
                conditional.then_label,
                conditional.else_label,
                conditional.merge_label,
                conditional.cond_idx,
                conditional.attr,
                &current_val,
                &mut builder,
                liveness.as_ref(),
            ) {
                // Collect fresh variables for then/else blocks from all insertions
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
                    label_to_fresh_vars.insert(conditional.then_label, fresh_vars_for_then_block);
                }
                if !fresh_vars_for_else_block.is_empty() {
                    label_to_fresh_vars.insert(conditional.else_label, fresh_vars_for_else_block);
                }

                pending_inserts
                    .entry(insertion_label)
                    .or_default()
                    .extend(insertions);
            }
        }

        // Now emit the transformed code
        let mut pc = 0;
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

                            builder.set_next_debug_comment(format!(
                                "conditional_merge_insertion: merge assign t{} := t{}",
                                ins.dest_var, new_temp
                            ));
                            builder.emit_with(|id| {
                                Bytecode::Assign(id, ins.dest_var, new_temp, AssignKind::Store)
                            });
                            current_val.insert(ins.dest_var, new_temp);
                        }
                    }
                }
                Bytecode::Branch(attr, then_label, else_label, cond_idx) => {
                    // Just emit the branch - insertions are handled above
                    builder.emit(Bytecode::Branch(attr, then_label, else_label, cond_idx))
                }
                Bytecode::Assign(attr, original_dst, src, kind) => {
                    let fresh_dst = active_fresh_vars
                        .get(&original_dst)
                        .copied()
                        .unwrap_or(original_dst);
                    current_val.insert(original_dst, src); // Track latest rhs value of original dst
                    builder.emit(Bytecode::Assign(attr, fresh_dst, src, kind))
                }
                Bytecode::Call(attr, dests, op, srcs, abort) if dests.len() == 1 => {
                    let original_dest = dests[0];
                    let actual_dest = active_fresh_vars
                        .get(&original_dest)
                        .copied()
                        .unwrap_or(original_dest);
                    current_val.insert(original_dest, original_dest);
                    builder.emit(Bytecode::Call(attr, vec![actual_dest], op, srcs, abort))
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

impl ConditionalMergeInsertionProcessor {
    // Find all conditional structures in the function
    fn find_all_conditionals(
        &self,
        code: &[Bytecode],
        back_cfg: &StacklessControlFlowGraph,
    ) -> Vec<ConditionalInfo> {
        let mut conditionals = Vec::new();

        for (pc, bytecode) in code.iter().enumerate() {
            if let Bytecode::Branch(attr, then_label, else_label, cond_idx) = bytecode {
                if let Some(merge_label) = self.find_merge_by_dominators(code, back_cfg, pc) {
                    conditionals.push(ConditionalInfo {
                        pc,
                        attr: *attr,
                        then_label: *then_label,
                        else_label: *else_label,
                        merge_label,
                        cond_idx: *cond_idx,
                    });
                }
            }
        }

        // Sort by merge label position (process inner-most first)
        let labels = Bytecode::label_offsets(code);
        conditionals.sort_by_key(|c| labels.get(&c.merge_label).unwrap_or(&0));

        conditionals
    }
}

#[derive(Clone, Debug)]
struct ConditionalInfo {
    pc: usize,
    attr: AttrId,
    then_label: Label,
    else_label: Label,
    merge_label: Label,
    cond_idx: usize,
}
