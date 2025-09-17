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
    stackless_bytecode::{AssignKind, AttrId, Bytecode, Label, Operation},
    stackless_control_flow_graph::StacklessControlFlowGraph,
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

    // Helper function to scan a block for simple assignments
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
    ) -> Option<(Label, Insertion)> {
        let labels = Bytecode::label_offsets(code);
        let then_pc = *labels.get(&then_label)? as usize;
        let else_pc = *labels.get(&else_label)? as usize;
        let merge_pc = *labels.get(&merge_label)? as usize;

        // Scan the then-block: from then_pc to else_pc
        let then_assignment = self.block_permitted(code, then_pc, else_pc)?;
        let (then_var, then_src) = then_assignment;

        // Scan the else-block: from else_pc to merge_pc
        // If else_pc == merge_pc, there's no else block (pure fallthrough)
        let else_assignment = if else_pc < merge_pc {
            self.block_permitted(code, else_pc, merge_pc)
        } else {
            None
        };

        let else_var = match else_assignment {
            Some((else_var_from_block, else_src)) => {
                // TODO(rvantonder): restriction: both blocks assign and must be same var
                if then_var != else_var_from_block {
                    return None;
                }
                // If-then-else pattern with explicit else source (same var)
                else_src
            }
            None => {
                // If-then (fallthrough): current_val is fallthrough source var
                *current_val.get(&then_var).unwrap_or(&then_var)
            }
        };

        let insertion = Insertion {
            dest_var: then_var,
            cond: cond_idx,
            then_var: then_src,
            src_attr,
            else_var,
        };

        Some((merge_label, insertion))
    }
}

#[derive(Clone, Debug)]
struct Insertion {
    src_attr: AttrId,
    dest_var: usize,
    cond: usize,
    then_var: usize,
    else_var: usize,
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
                            let var_ty = builder.get_local_type(ins.dest_var);
                            let new_temp = builder.new_temp(var_ty);
                            builder.set_next_debug_comment(format!(
                                "conditional_merge_insertion: t{} := if_then_else(t{}, t{}, t{})",
                                new_temp, ins.cond, ins.then_var, ins.else_var
                            ));
                            builder.emit_with(|id| {
                                Bytecode::Call(
                                    id,
                                    vec![new_temp],
                                    Operation::IfThenElse,
                                    vec![ins.cond, ins.then_var, ins.else_var],
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
                    let merge_label =
                        self.find_merge_by_dominators(&orig_code, back_cfg.as_ref().unwrap(), pc);

                    if merge_label.is_none() {
                        builder.emit(Bytecode::Branch(attr, then_label, else_label, cond_idx));
                        continue;
                    }
                    // Invariant: merge_label is Some
                    let merge_label = merge_label.unwrap();
                    if let Some((insertion_label, insertion)) = self.build_conditional_insert(
                        &orig_code,
                        then_label,
                        else_label,
                        merge_label,
                        cond_idx,
                        attr,
                        &current_val,
                    ) {
                        pending_inserts
                            .entry(insertion_label)
                            .or_default()
                            .push(insertion);
                    }
                    builder.emit(Bytecode::Branch(attr, then_label, else_label, cond_idx))
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
