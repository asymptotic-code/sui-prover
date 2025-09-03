// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use move_binary_format::file_format::CodeOffset;
use move_model::{
    model::FunctionEnv,
    ty::{PrimitiveType, Type},
};

use crate::{
    ast::TempIndex,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    graph::{DomRelation, Graph},
    stackless_bytecode::{AttrId, Bytecode, Label, Operation},
    stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph},
};

pub struct SSATransformProcessor {
    debug: bool,
}

impl SSATransformProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self { debug: false })
    }

    pub fn new_with_debug() -> Box<Self> {
        Box::new(Self { debug: true })
    }

    fn collect_conditionals(
        &self,
        target: &FunctionTarget<'_>,
        cfg: &StacklessControlFlowGraph,
    ) -> Vec<ConditionalPattern> {
        let mut conditionals = Vec::new();
        let code = &target.data.code;

        for (pc, bytecode) in code.iter().enumerate() {
            if let Bytecode::Branch(_attr_id, true_label, false_label, condition) = bytecode {
                if self.debug {
                    println!("Found branch at PC {} with condition {:?}", pc, condition);
                }

                if let Some(cond) = self.analyze_conditional(
                    target,
                    cfg,
                    pc as CodeOffset,
                    *true_label,
                    *false_label,
                    *condition,
                ) {
                    conditionals.push(cond);
                }
            }
        }

        if self.debug {
            println!("Found {} conditionals", conditionals.len());
        }

        conditionals
    }

    fn analyze_conditional(
        &self,
        target: &FunctionTarget<'_>,
        cfg: &StacklessControlFlowGraph,
        branch_pc: CodeOffset,
        true_label: Label,
        false_label: Label,
        condition: TempIndex,
    ) -> Option<ConditionalPattern> {
        let code = &target.data.code;
        let label_offsets = Bytecode::label_offsets(code);

        let true_pc = *label_offsets.get(&true_label)?;
        let false_pc = *label_offsets.get(&false_label)?;

        let true_block = self.pc_to_block(cfg, true_pc)?;
        let false_block = self.pc_to_block(cfg, false_pc)?;

        let merge_point = self.find_merge_point(cfg, true_block, false_block)?;

        let true_branch = self.collect_assignments(target, cfg, true_block);
        let false_branch = self.collect_assignments(target, cfg, false_block);

        // Variables assigned in both branches need phi node tracking
        let mut phi_vars = BTreeSet::new();
        for var in true_branch.keys() {
            if false_branch.contains_key(var) {
                phi_vars.insert(*var);
            }
        }

        // Check intersection of branch assignments is not empty.
        if phi_vars.is_empty() {
            return None;
        }

        Some(ConditionalPattern {
            condition,
            branch_pc,
            true_branch,
            false_branch,
            phi_vars,
            merge_pc: self.get_block_start_pc(cfg, merge_point)?,
        })
    }

    /// CFG -> dominator analysis -> Block merge point
    fn find_merge_point(
        &self,
        cfg: &StacklessControlFlowGraph,
        true_block: BlockId,
        false_block: BlockId,
    ) -> Option<BlockId> {
        let entry = cfg.entry_block();
        let nodes = cfg.blocks();
        let edges: Vec<(BlockId, BlockId)> = nodes
            .iter()
            .flat_map(|x| {
                cfg.successors(*x)
                    .iter()
                    .map(|y| (*x, *y))
                    .collect::<Vec<(BlockId, BlockId)>>()
            })
            .collect();
        let graph = Graph::new(entry, nodes.clone(), edges);
        let dom_relation = DomRelation::new(&graph);

        // Find all reachable blocks that could be merge points
        let reachable_blocks: Vec<_> = nodes
            .into_iter()
            .filter(|&block| dom_relation.is_reachable(block))
            .collect();

        // The merge point should be a block that is reachable from both
        // branches and is the closest common post-dominator
        for &candidate in &reachable_blocks {
            // Check if this candidate can be reached from both branches
            if self.can_reach_block(cfg, true_block, candidate)
                && self.can_reach_block(cfg, false_block, candidate)
            {
                // This is a potential merge point - verify it's the immediate
                // post-dominator by checking no other valid merge point
                // dominates this one
                let mut is_immediate = true;
                for &other in &reachable_blocks {
                    if other != candidate
                        && self.can_reach_block(cfg, true_block, other)
                        && self.can_reach_block(cfg, false_block, other)
                        && dom_relation.is_dominated_by(candidate, other)
                    {
                        is_immediate = false;
                        break;
                    }
                }
                if is_immediate {
                    return Some(candidate);
                }
            }
        }

        None
    }

    /// Check if we can reach target_block from start_block in the CFG
    fn can_reach_block(
        &self,
        cfg: &StacklessControlFlowGraph,
        start_block: BlockId,
        target_block: BlockId,
    ) -> bool {
        if start_block == target_block {
            return true;
        }

        let mut visited = BTreeSet::new();
        let mut queue = vec![start_block];
        visited.insert(start_block);

        while let Some(current) = queue.pop() {
            for &successor in cfg.successors(current) {
                if successor == target_block {
                    return true;
                }
                if !visited.contains(&successor) {
                    visited.insert(successor);
                    queue.push(successor);
                }
            }
        }

        false
    }

    /// Collect assignments in a bytecode block
    fn collect_assignments(
        &self,
        target: &FunctionTarget<'_>,
        cfg: &StacklessControlFlowGraph,
        block_id: BlockId,
    ) -> BTreeMap<TempIndex, TempIndex> {
        let mut assignments = BTreeMap::new();
        let code = &target.data.code;

        if let Some(range) = cfg.instr_indexes(block_id) {
            for pc in range {
                if let Some(bytecode) = code.get(pc as usize) {
                    if let Bytecode::Assign(_, dest, src, _) = bytecode {
                        assignments.insert(*dest, *src);
                    }
                    // XXX: calls that assign to destinations?
                }
            }
        }

        assignments
    }

    fn pc_to_block(&self, cfg: &StacklessControlFlowGraph, pc: CodeOffset) -> Option<BlockId> {
        for block_id in cfg.blocks() {
            if let Some(range) = cfg.instr_indexes(block_id) {
                for offset in range {
                    if offset == pc {
                        return Some(block_id);
                    }
                }
            }
        }
        None
    }

    fn get_block_start_pc(
        &self,
        cfg: &StacklessControlFlowGraph,
        block_id: BlockId,
    ) -> Option<CodeOffset> {
        match cfg.content(block_id) {
            BlockContent::Basic { lower, .. } => Some(*lower),
            BlockContent::Dummy => None,
        }
    }

    fn transform_to_ssa(
        &self,
        target: &FunctionTarget<'_>,
        conditionals: Vec<ConditionalPattern>,
    ) -> (Vec<Bytecode>, usize, BTreeMap<TempIndex, TempIndex>) {
        // Invariant: conditionals is non-empty

        let mut new_code = Vec::new();
        let mut ssa_ctx = SSAContext::default();
        let code = &target.data.code;

        ssa_ctx.next_temp = target.get_local_count();
        if self.debug {
            println!(
                "Transforming {} conditionals to SSA form",
                conditionals.len()
            );
        }

        let mut processed_locs = BTreeSet::new();

        for (pc, bytecode) in code.iter().enumerate() {
            let pc = pc as CodeOffset;
            if processed_locs.contains(&pc) {
                continue;
            }
            if let Some(conditional) = conditionals.iter().find(|p| p.branch_pc == pc) {
                if self.debug {
                    println!("Transforming conditional pattern at PC {}", pc);
                    println!("  Condition: {:?}", conditional.condition);
                    println!("  True assignments: {:?}", conditional.true_branch);
                    println!("  False assignments: {:?}", conditional.false_branch);
                    println!("  Phi vars: {:?}", conditional.phi_vars);
                }

                let conditional_bytecode = self.transform_conditional(conditional, &mut ssa_ctx);
                new_code.extend(conditional_bytecode);
                self.mark_conditional_locs_processed(target, conditional, &mut processed_locs);
            } else {
                // Regular instruction
                let transformed_instruction =
                    self.rename_variables_in_instruction(bytecode, &mut ssa_ctx);
                new_code.push(transformed_instruction);
                processed_locs.insert(pc);
            }
        }

        if self.debug {
            println!(
                "SSA transformation completed. Generated {} instructions from {} original",
                new_code.len(),
                code.len()
            );
        }

        (new_code, ssa_ctx.next_temp, ssa_ctx.temp_origins)
    }

    fn transform_conditional(
        &self,
        conditional: &ConditionalPattern,
        ssa_ctx: &mut SSAContext,
    ) -> Vec<Bytecode> {
        let mut result = Vec::new();

        // For each variable that gets assigned in both branches (phi variables)
        for &phi_var in &conditional.phi_vars {
            // Get the values assigned in then/else branches
            let true_value = conditional
                .true_branch
                .get(&phi_var)
                .copied()
                .unwrap_or(phi_var); // Default to original if no assignment
            let false_value = conditional
                .false_branch
                .get(&phi_var)
                .copied()
                .unwrap_or(phi_var); // Default to original if no assignment

            // Create new SSA temporary for the merged value
            let merge_point_temp_var = self.create_ssa_temp(ssa_ctx, phi_var, 0);

            if self.debug {
                println!(
                    "Creating TernaryConditional: {} = if {:?} then {:?} else {:?}",
                    merge_point_temp_var, conditional.condition, true_value, false_value
                );
            }

            // Generate TernaryConditional operation
            // Call(attr, dests, oper, srcs, abort_action)
            let ternary_conditional = Bytecode::Call(
                AttrId::new(conditional.branch_pc as usize), // Branch PC is attr
                vec![merge_point_temp_var],                  // Destination: merged temp
                Operation::TernaryConditional,
                vec![conditional.condition, true_value, false_value], // Sources: condition, true_value, false_value
                None,                                                 // No abort action
            );

            result.push(ternary_conditional);

            // Update SSA context to map original variable to new temp
            ssa_ctx.current_version.insert(phi_var, 1);
            ssa_ctx
                .version_map
                .insert((phi_var, 1), merge_point_temp_var);
        }

        result
    }

    fn mark_conditional_locs_processed(
        &self,
        target: &FunctionTarget<'_>,
        conditional: &ConditionalPattern,
        processed_locs: &mut BTreeSet<CodeOffset>,
    ) {
        // Mark the branch instruction
        processed_locs.insert(conditional.branch_pc);

        // Mark instructions in then/else blocks
        // For simplicity, we'll mark a range around the merge point
        // In a full implementation, we'd track exact block boundaries
        let code = &target.data.code;
        let start_pc = conditional.branch_pc;
        let end_pc = std::cmp::min(conditional.merge_pc + 5, code.len() as CodeOffset);

        for pc in start_pc..end_pc {
            processed_locs.insert(pc);
        }
    }

    /// Rename variables in a regular (non-conditional) instruction based on SSA context
    fn rename_variables_in_instruction(
        &self,
        bytecode: &Bytecode,
        ssa_ctx: &mut SSAContext,
    ) -> Bytecode {
        use Bytecode::*;

        match bytecode {
            // Handle assignments: dest = src
            Assign(attr, dest, src, assign_kind) => {
                // Rename source variable to its latest SSA version
                let renamed_src = self.get_current_ssa_version(*src, ssa_ctx);

                // Create new SSA version for destination
                let new_dest = self.create_new_ssa_version(*dest, ssa_ctx);

                Assign(attr.clone(), new_dest, renamed_src, *assign_kind)
            }

            // Handle calls: may have multiple sources and destinations
            Call(attr, dests, oper, srcs, abort_action) => {
                // Rename all source variables
                let renamed_srcs: Vec<TempIndex> = srcs
                    .iter()
                    .map(|&src| self.get_current_ssa_version(src, ssa_ctx))
                    .collect();

                // Create new SSA versions for destinations
                let new_dests: Vec<TempIndex> = dests
                    .iter()
                    .map(|&dest| self.create_new_ssa_version(dest, ssa_ctx))
                    .collect();

                Call(
                    attr.clone(),
                    new_dests,
                    oper.clone(),
                    renamed_srcs,
                    abort_action.clone(),
                )
            }

            // Handle other instructions that may reference variables
            Load(attr, dest, constant) => {
                let new_dest = self.create_new_ssa_version(*dest, ssa_ctx);
                Load(attr.clone(), new_dest, constant.clone())
            }

            // Most other instructions don't need renaming
            _ => bytecode.clone(),
        }
    }

    fn get_current_ssa_version(&self, original: TempIndex, ssa_ctx: &mut SSAContext) -> TempIndex {
        let current_version = ssa_ctx.current_version.get(&original).copied().unwrap_or(0);

        // Check if we already have a mapping for this version
        if let Some(&ssa_temp) = ssa_ctx.version_map.get(&(original, current_version)) {
            ssa_temp
        } else {
            // If this is version 0 and no mapping exists, use original temp
            if current_version == 0 {
                original
            } else {
                // Create a new temp for this version
                let new_temp = ssa_ctx.next_temp;
                ssa_ctx.next_temp += 1;
                ssa_ctx
                    .version_map
                    .insert((original, current_version), new_temp);
                ssa_ctx.temp_origins.insert(new_temp, original);
                new_temp
            }
        }
    }

    /// Create a new SSA version for a variable being assigned to
    fn create_new_ssa_version(&self, original: TempIndex, ssa_ctx: &mut SSAContext) -> TempIndex {
        // Increment the version for this variable
        let new_version = ssa_ctx.current_version.get(&original).copied().unwrap_or(0) + 1;
        ssa_ctx.current_version.insert(original, new_version);

        // Create new temp index for this version
        let new_temp = ssa_ctx.next_temp;
        ssa_ctx.next_temp += 1;
        ssa_ctx
            .version_map
            .insert((original, new_version), new_temp);
        ssa_ctx.temp_origins.insert(new_temp, original);

        new_temp
    }

    /// Create a new temporary index for SSA
    fn create_ssa_temp(
        &self,
        ctx: &mut SSAContext,
        original: TempIndex,
        version: usize,
    ) -> TempIndex {
        if let Some(&existing) = ctx.version_map.get(&(original, version)) {
            return existing;
        }

        let new_temp = ctx.next_temp;
        ctx.next_temp += 1;
        ctx.version_map.insert((original, version), new_temp);
        ctx.temp_origins.insert(new_temp, original);
        new_temp
    }
}

/// Conditional expression state
#[derive(Debug, Clone)]
struct ConditionalPattern {
    condition: TempIndex,
    branch_pc: CodeOffset,
    /// Represents block of assignments: temp_var -> value
    true_branch: BTreeMap<TempIndex, TempIndex>,
    false_branch: BTreeMap<TempIndex, TempIndex>,
    /// Phi nodes for variables at merge point
    phi_vars: BTreeSet<TempIndex>,
    merge_pc: CodeOffset,
}

/// SSA variable tracking and renaming
#[derive(Debug, Default)]
struct SSAContext {
    /// Track the current temp_var version (each temp_var has a version)
    current_version: BTreeMap<TempIndex, usize>,
    /// Next free variable
    next_temp: TempIndex,
    /// Version tracking: (prev_temp_var, version) -> new_temp_var
    version_map: BTreeMap<(TempIndex, usize), TempIndex>,
    /// Map new temp to original for type infrerence
    temp_origins: BTreeMap<TempIndex, TempIndex>,
}

impl FunctionTargetProcessor for SSATransformProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        if self.debug {
            println!(
                "Processing function {} for SSA transformation",
                func_env.get_full_name_str()
            );
        }

        let target = FunctionTarget::new(func_env, &data);
        let cfg = StacklessControlFlowGraph::new_forward(&data.code);
        let conditionals = self.collect_conditionals(&target, &cfg);

        if conditionals.is_empty() {
            return data;
        }

        let (new_code, max_temp_used, temp_origins) = self.transform_to_ssa(&target, conditionals);

        // replace function data
        data.code = new_code;

        // Update local_types to include new temporaries created during SSA transformation
        let original_local_count = data.local_types.len();
        while data.local_types.len() < max_temp_used {
            // For new SSA temporaries, we need to determine their type
            let new_temp_index = data.local_types.len();
            let temp_type = if new_temp_index < original_local_count {
                // This is an existing temporary
                data.local_types[new_temp_index].clone()
            } else if let Some(&original_temp) = temp_origins.get(&new_temp_index) {
                // This is a new SSA temporary derived from an original temp
                data.local_types[original_temp].clone()
            } else {
                // Fallback - use a reasonable default type
                if !data.local_types.is_empty() {
                    data.local_types[0].clone()
                } else {
                    Type::Primitive(PrimitiveType::U64)
                }
            };
            data.local_types.push(temp_type);
        }

        if self.debug {
            println!(
                "SSA transformation completed for {}",
                func_env.get_full_name_str()
            );
        }

        data
    }

    fn name(&self) -> String {
        "ssa_transform".to_owned()
    }
}
