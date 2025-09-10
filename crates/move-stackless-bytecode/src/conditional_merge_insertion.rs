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
//! This leaves branch-local assignments in place (they may be dead after merge
//! and can be cleaned up by later passes).

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    graph::{DomRelation, Graph},
    stackless_bytecode::{AttrId, Bytecode, Operation},
    stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph},
};
use move_model::model::FunctionEnv;

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

    fn next_attr_pair(data: &FunctionData) -> (AttrId, AttrId) {
        let base = data.next_free_attr_index();
        (AttrId::new(base), AttrId::new(base + 1))
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
            Bytecode::Branch(_, tl, _el, cond) => (tl, *cond as usize),
            _ => return None,
        };

        let labels = Bytecode::label_offsets(code);
        let then_pc = *labels.get(then_label)? as usize;
        let branch_block = Self::pc_to_block(back_cfg, branch_pc as u16)?;

        // Compute merge block as immediate post-dominator of the branch block using
        // reversed-graph dominator analysis (postdominators of the original graph).
        let merge_block = Self::find_immediate_post_dominator(back_cfg, branch_block)?;
        let merge_pc = Self::block_start_pc(back_cfg, merge_block)? as usize;

        Some((cond, then_pc, merge_pc))
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

    // Return the last assignment (dst:=src) in the then block before merge
    fn then_branch_last_var_assign(
        code: &[Bytecode],
        then_start_pc: usize,
        merge_label_pc: usize,
    ) -> Option<(usize /*var*/, usize /*then_src*/)> {
        let mut result: Option<(usize, usize)> = None;
        let mut pc = then_start_pc;
        while pc < code.len() && pc < merge_label_pc {
            match &code[pc] {
                Bytecode::Assign(_, dst, src, _) => {
                    result = Some((*dst as usize, *src as usize));
                }
                // If we see a call writing directly to a var, take var itself as then_src
                Bytecode::Call(_, dests, _op, _srcs, _) if !dests.is_empty() => {
                    let var = dests[0] as usize;
                    result = Some((var, var));
                }
                _ => {}
            }
            if code[pc].is_unconditional_branch() {
                break;
            }
            pc += 1;
        }
        result
    }

    // Scan backwards before `branch_pc` to find the last assignment to `var` for else-path.
    fn else_var_before_branch(code: &[Bytecode], branch_pc: usize, var: usize) -> Option<usize> {
        let mut pc: isize = branch_pc as isize - 1;
        while pc >= 0 {
            match &code[pc as usize] {
                Bytecode::Assign(_, dst, src, _) if *dst as usize == var => {
                    return Some(*src as usize);
                }
                _ => {}
            }
            pc -= 1;
        }
        None
    }
}

impl FunctionTargetProcessor for ConditionalMergeInsertionProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        _func_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let mut pc = 0;
        while pc < data.code.len() {
            if matches!(data.code[pc], Bytecode::Branch(..)) {
                // Build backward CFG after any mutations to code to keep mapping fresh
                let back_cfg = StacklessControlFlowGraph::new_backward(&data.code, false);
                if let Some((cond, then_start, merge_pc)) =
                    Self::find_merge_by_dominators(&data.code, &back_cfg, pc)
                {
                    if let Some((var, then_src)) =
                        Self::then_branch_last_var_assign(&data.code, then_start, merge_pc)
                    {
                        if let Some(else_src) = Self::else_var_before_branch(&data.code, pc, var) {
                            let insert_at =
                                if matches!(data.code.get(merge_pc), Some(Bytecode::Label(..))) {
                                    // In case of label / jump dest, insert after.
                                    merge_pc + 1
                                } else {
                                    merge_pc
                                };

                            // Allocate a fresh temp of same type as `var`
                            let new_temp = data.local_types.len();
                            let var_ty = data.local_types[var].clone();
                            data.local_types.push(var_ty);

                            let (ite_attr, assign_attr) = Self::next_attr_pair(&data);

                            // t_new := if_then_else(cond, then_src, else_src)
                            let ite = Bytecode::Call(
                                ite_attr,
                                vec![new_temp],
                                Operation::IfThenElse,
                                vec![cond, then_src, else_src],
                                None,
                            );
                            // var := t_new
                            let assign = Bytecode::Assign(
                                assign_attr,
                                var,
                                new_temp,
                                crate::stackless_bytecode::AssignKind::Copy,
                            );

                            if self.debug {
                                eprintln!(
                                    "[conditional_merge_insertion] insert@{}: t{} := if_then_else(t{}, t{}, t{}); t{} := t{}",
                                    insert_at, new_temp, cond, then_src, else_src, var, new_temp
                                );
                            }

                            data.debug_comments.insert(
                                ite_attr,
                                format!(
                                    "conditional_merge_insertion: t{} := if_then_else(t{}, t{}, t{})",
                                    new_temp, cond, then_src, else_src
                                ),
                            );
                            data.debug_comments.insert(
                                assign_attr,
                                format!(
                                    "conditional_merge_insertion: merge assign t{} := t{}",
                                    var, new_temp
                                ),
                            );

                            // Insert and skip past assign
                            data.code.splice(insert_at..insert_at, [ite, assign]);
                            pc = insert_at + 2;
                            continue;
                        }
                    }
                }
            }

            pc += 1;
        }

        data
    }

    fn name(&self) -> String {
        "conditional_merge_insertion".to_string()
    }
}
