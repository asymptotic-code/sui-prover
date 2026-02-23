// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! SSA-style conditional merge insertion for variables assigned multiple times.
//!
//! Algorithm:
//! 1. Collect all variables assigned multiple times
//! 2. Use control flow reconstruction to get the structured control flow graph
//! 3. Compute variable completion points (last if-then-else block with a merge instruction)
//! 4. Walk the structured graph, tracking variable versions and collecting pending merges
//!    (`fresh := if_then_else(cond, then_ver, else_ver)`)
//! 5. Insert pending merges in a linear pass
//!
//! Conditions:
//! - No loops
//! - No mutable references

use crate::{
    control_flow_reconstruction::{reconstruct_control_flow, StructuredBlock},
    exp_generator::ExpGenerator,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
};
use codespan_reporting::diagnostic::Severity;
use itertools::Itertools;
use move_binary_format::file_format::CodeOffset;
use move_model::model::FunctionEnv;
use std::collections::{BTreeMap, BTreeSet};

/// Information about a merge instruction to be emitted
/// (`fresh := if_then_else(cond, then_ver, else_ver)`)
struct MergeInfo {
    /// Fresh variable for the merge result
    fresh: usize,
    /// Condition variable for the if-then-else block
    cond: usize,
    /// Version from the then-branch
    then_ver: usize,
    /// Version from the else-branch
    else_ver: usize,
}

/// State maintained during the structured control flow walk.
struct VersionState<'env> {
    /// Current version of each variable (initialized to original variable as placeholder).
    current_version: BTreeMap<usize, usize>,
    /// Pending merges at each PC.
    merges_at: BTreeMap<CodeOffset, Vec<MergeInfo>>,
    /// Variables that have been fully processed (merged back to original variable).
    completed: BTreeSet<usize>,
    /// Completion PC for each variable (last if-then-else block with a merge instruction).
    completed_at: BTreeMap<usize, CodeOffset>,
    /// Builder for modifying bytecode and creating fresh temporary variables.
    builder: FunctionDataBuilder<'env>,
}

impl<'env> VersionState<'env> {
    fn new(builder: FunctionDataBuilder<'env>) -> Self {
        Self {
            current_version: BTreeMap::new(),
            merges_at: BTreeMap::new(),
            completed_at: BTreeMap::new(),
            completed: BTreeSet::new(),
            builder,
        }
    }

    /// Merge multiple `Ret` instructions into a single `Ret` using `IfThenElse`.
    /// Walks the structured control flow to find the return temp for each branch,
    /// collects `IfThenElse` merges where branches return different values, then
    /// replaces all `Ret` instructions with `Nop` and appends the merges + single `Ret`.
    fn merge_returns(&mut self, structured: &StructuredBlock) {
        let mut merges = Vec::new();
        let Some(merged_ret) = self.merge_return_temp(structured, &mut merges) else {
            return;
        };

        // replace all Ret instructions with Nop
        for bc in &mut self.builder.data.code {
            if matches!(bc, Bytecode::Ret(..)) {
                *bc = Bytecode::Nop(bc.get_attr_id());
            }
        }

        // emit collected merges, then single Ret
        for merge in &merges {
            self.builder.set_next_debug_comment(format!(
                "conditional_merge_insertion: t{} := if_then_else(t{}, t{}, t{})",
                merge.fresh, merge.cond, merge.then_ver, merge.else_ver
            ));
            self.builder.emit_with(|id| {
                Bytecode::Call(
                    id,
                    vec![merge.fresh],
                    Operation::IfThenElse,
                    vec![merge.cond, merge.then_ver, merge.else_ver],
                    None,
                )
            });
        }
        let attr = self.builder.new_attr();
        self.builder
            .data
            .code
            .push(Bytecode::Ret(attr, vec![merged_ret]));
    }

    /// Recursively find (or create) the return temp for a structured block.
    /// When an `IfThenElse` has branches returning different temps, a merge is
    /// collected and the fresh result temp is returned.
    fn merge_return_temp(
        &mut self,
        block: &StructuredBlock,
        merges: &mut Vec<MergeInfo>,
    ) -> Option<usize> {
        match block {
            StructuredBlock::Basic { lower, upper } => {
                for pc in (*lower..=*upper).rev() {
                    if let Bytecode::Ret(_, srcs) = &self.builder.data.code[pc as usize] {
                        return srcs.first().copied();
                    }
                }
                None
            }
            StructuredBlock::Seq(blocks) => {
                for b in blocks.iter().rev() {
                    if let Some(t) = self.merge_return_temp(b, merges) {
                        return Some(t);
                    }
                }
                None
            }
            StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch,
            } => {
                let then_ret = self.merge_return_temp(then_branch, merges);
                let else_ret = else_branch
                    .as_ref()
                    .and_then(|b| self.merge_return_temp(b, merges));

                match (then_ret, else_ret) {
                    (Some(t), Some(e)) if t == e => Some(t),
                    (Some(t), Some(e)) => {
                        let cond = match &self.builder.data.code[*cond_at as usize] {
                            Bytecode::Branch(_, _, _, c) => *c,
                            _ => return None,
                        };
                        let ret_type = self.builder.get_local_type(t);
                        let fresh = self.builder.add_local(ret_type);
                        merges.push(MergeInfo {
                            fresh,
                            cond,
                            then_ver: t,
                            else_ver: e,
                        });
                        Some(fresh)
                    }
                    (Some(t), None) => Some(t),
                    (None, Some(e)) => Some(e),
                    (None, None) => None,
                }
            }
            StructuredBlock::IfElseChain { .. } => {
                self.merge_return_temp(&block.clone().chain_to_if_then_else(), merges)
            }
        }
    }

    /// Collect variables assigned multiple times and initialize the current version
    /// of each variable to itself (placeholder).
    fn collect_multi_assigned_vars(&mut self) {
        let mut assignment_counts: BTreeMap<usize, usize> = BTreeMap::new();

        for bc in &self.builder.data.code {
            for dest in bc.dests() {
                *assignment_counts.entry(dest).or_default() += 1;
            }
        }

        // filter to only variables assigned more than once, map each to itself
        self.current_version = assignment_counts
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .map(|(var, _)| (var, var))
            .collect();
    }

    /// Compute for each variable the last if-then-else block with a merge instruction.
    /// Returns the set of multi-assigned variables assigned in this block.
    fn compute_completed_at(
        &mut self,
        block: &StructuredBlock,
        assigned_before: &BTreeSet<usize>,
    ) -> BTreeSet<usize> {
        match block {
            StructuredBlock::Basic { lower, upper } => {
                let mut assigned = BTreeSet::new();
                for pc in *lower..=*upper {
                    for dest in self.builder.data.code[pc as usize].dests() {
                        if self.current_version.contains_key(&dest) {
                            assigned.insert(dest);
                        }
                    }
                }
                assigned
            }
            StructuredBlock::Seq(blocks) => {
                let mut assigned_before_child = assigned_before.clone();
                let mut assigned = BTreeSet::new();
                for child in blocks {
                    let assigned_in_child =
                        self.compute_completed_at(child, &assigned_before_child);
                    assigned_before_child.extend(assigned_in_child.iter().copied());
                    assigned.extend(assigned_in_child);
                }
                assigned
            }
            StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch,
            } => {
                let assigned_in_then = self.compute_completed_at(then_branch, assigned_before);
                let assigned_in_else = match else_branch {
                    Some(else_block) => self.compute_completed_at(else_block, assigned_before),
                    None => BTreeSet::new(),
                };

                // what's known (non-placeholder) on each side
                let then_known: BTreeSet<_> =
                    assigned_before.union(&assigned_in_then).copied().collect();
                let else_known: BTreeSet<_> =
                    assigned_before.union(&assigned_in_else).copied().collect();

                // a merge is created if the variable is known on both sides and newly assigned in at least one
                for var in then_known.intersection(&else_known) {
                    if assigned_in_then.contains(var) || assigned_in_else.contains(var) {
                        self.completed_at.insert(*var, *cond_at);
                    }
                }

                // return what was assigned in this if-then-else (union of both branches)
                assigned_in_then.union(&assigned_in_else).copied().collect()
            }
            StructuredBlock::IfElseChain { .. } => {
                self.compute_completed_at(&block.clone().chain_to_if_then_else(), assigned_before)
            }
        }
    }

    /// Walk the structured control flow, tracking versions, collecting merges,
    /// and performing substitutions.
    fn process_block(&mut self, block: &StructuredBlock) -> Vec<MergeInfo> {
        match block {
            StructuredBlock::Basic { lower, upper } => {
                for pc in *lower..=*upper {
                    self.process_instruction(pc);
                }
                Vec::new()
            }
            StructuredBlock::Seq(blocks) => {
                let mut merges = Vec::new();
                for child in blocks {
                    // store pending merges at the start of this child
                    self.merges_at.insert(
                        child.iter_offsets().next().unwrap(),
                        std::mem::take(&mut merges),
                    );
                    // process the child
                    merges = self.process_block(child);
                }
                merges
            }
            StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch,
            } => self.process_if_then_else(*cond_at, then_branch, else_branch.as_deref()),
            StructuredBlock::IfElseChain { .. } => {
                self.process_block(&block.clone().chain_to_if_then_else())
            }
        }
    }

    /// Process a single instruction, updating the current version of each variable and
    /// performing substitutions.
    fn process_instruction(&mut self, pc: CodeOffset) {
        // substitute source variables with their current version
        self.builder.data.code[pc as usize] = self.builder.data.code[pc as usize]
            .clone()
            .remap_src_vars(self.builder.global_env(), &mut |x| {
                if self.completed.contains(&x) {
                    x
                } else {
                    self.current_version.get(&x).copied().unwrap_or(x)
                }
            });

        for dest in self.builder.data.code[pc as usize].dests().collect_vec() {
            // only process multi-assigned variables
            if self.current_version.contains_key(&dest) {
                let fresh = self.builder.new_temp(self.builder.get_local_type(dest));
                self.current_version.insert(dest, fresh);
                self.builder.data.code[pc as usize] = self.builder.data.code[pc as usize]
                    .clone()
                    .remap_dest_vars(self.builder.global_env(), &mut |x| {
                        if x == dest {
                            fresh
                        } else {
                            x
                        }
                    });
            }
        }
    }

    /// Process an if-then-else block, creating merges for divergent versions.
    fn process_if_then_else(
        &mut self,
        cond_at: CodeOffset,
        then_branch: &StructuredBlock,
        else_branch: Option<&StructuredBlock>,
    ) -> Vec<MergeInfo> {
        // extract condition variable from the Branch instruction
        let cond = match &self.builder.data.code[cond_at as usize] {
            Bytecode::Branch(_, _, _, cond) => *cond,
            _ => unreachable!(
                "expected branch instruction, found {:?}",
                self.builder.data.code[cond_at as usize]
            ),
        };

        // process then-branch
        let saved_versions = self.current_version.clone();
        let mut merges = self.process_block(then_branch);
        let then_versions = std::mem::replace(&mut self.current_version, saved_versions);

        // process else-branch (if present)
        if let Some(else_block) = else_branch {
            merges.extend(self.process_block(else_block));
        }
        let else_versions = self.current_version.clone();

        // for each variable where versions diverge, create a merge
        for (&var, &then_ver) in &then_versions {
            let else_ver = else_versions[&var];
            if then_ver != else_ver {
                assert!(
                    then_ver != var,
                    "then_ver is the original variable {} at pc {}",
                    var,
                    cond_at
                );
                assert!(
                    else_ver != var,
                    "else_ver is the original variable {} at pc {}",
                    var,
                    cond_at
                );
                let fresh = if self.completed_at.get(&var) == Some(&cond_at) {
                    self.completed.insert(var);
                    var
                } else {
                    let var_ty = self.builder.get_local_type(var);
                    self.builder.new_temp(var_ty)
                };
                self.current_version.insert(var, fresh);
                merges.push(MergeInfo {
                    fresh,
                    cond,
                    then_ver,
                    else_ver,
                });
            }
        }

        merges
    }

    /// Emit the transformed bytecode with merge instructions.
    fn emit_merges(&mut self) {
        let code = std::mem::take(&mut self.builder.data.code);
        for (pc, bc) in code.into_iter().enumerate() {
            self.builder.emit(bc);

            // emit merge instructions scheduled at this PC
            for merge in self
                .merges_at
                .get(&(pc as CodeOffset))
                .unwrap_or(&Vec::new())
                .iter()
            {
                self.builder.set_next_debug_comment(format!(
                    "conditional_merge_insertion: t{} := if_then_else(t{}, t{}, t{})",
                    merge.fresh, merge.cond, merge.then_ver, merge.else_ver
                ));
                self.builder.emit_with(|id| {
                    Bytecode::Call(
                        id,
                        vec![merge.fresh],
                        Operation::IfThenElse,
                        vec![merge.cond, merge.then_ver, merge.else_ver],
                        None,
                    )
                });
            }
        }
    }
}

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
}

impl FunctionTargetProcessor for ConditionalMergeInsertionProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        // skip unless option is set or this is a pure function
        if !targets.prover_options().enable_conditional_merge_insertion
            && !self.debug
            && !targets.is_pure_fun(&func_env.get_qualified_id())
            && !targets.is_axiom_fun(&func_env.get_qualified_id())
        {
            return data;
        }

        if func_env.is_native() || func_env.is_intrinsic() {
            return data;
        }

        // cannot handle mutable references
        if data.local_types.iter().any(|ty| ty.is_mutable_reference()) {
            if targets.is_pure_fun(&func_env.get_qualified_id()) {
                func_env.module_env.env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    "Pure functions with mutable references are not supported",
                );
            }
            return data;
        }

        let is_pure = targets.is_pure_fun(&func_env.get_qualified_id())
            || targets.is_axiom_fun(&func_env.get_qualified_id());

        let builder = FunctionDataBuilder::new(func_env, data);
        let mut state = VersionState::new(builder);

        // step 1: collect all variables assigned multiple times
        state.collect_multi_assigned_vars();

        let ret_count = state
            .builder
            .data
            .code
            .iter()
            .filter(|bc| matches!(bc, Bytecode::Ret(..)))
            .count();

        if state.current_version.is_empty() && ret_count <= 1 {
            return state.builder.data;
        }

        // step 2: reconstruct control flow
        let structured_block = match reconstruct_control_flow(&state.builder.data.code) {
            Some(s) => s,
            None => {
                // cannot reconstruct (loops, switches, etc.)
                if is_pure {
                    func_env.module_env.env.diag(
                        Severity::Error,
                        &func_env.get_loc(),
                        "Pure functions with loops are not supported",
                    );
                }
                return state.builder.data;
            }
        };

        if !state.current_version.is_empty() {
            // step 3: compute where each variable completes (last if-then-else with a merge instruction)
            state.compute_completed_at(&structured_block, &BTreeSet::new());

            // step 4: traverse structured control flow, collecting merges
            state.process_block(&structured_block);

            // step 5: emit merges
            state.emit_merges();
        }

        // step 6: merge early returns for pure/axiom functions
        if is_pure && ret_count > 1 {
            state.merge_returns(&structured_block);
        }

        state.builder.data
    }

    fn name(&self) -> String {
        "conditional_merge_insertion".to_string()
    }
}
