// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use move_binary_format::file_format::CodeOffset;
use move_model::model::FunctionEnv;

use crate::{
    ast::TempIndex,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    graph::{DomRelation, Graph},
    stackless_bytecode::{Bytecode, Label},
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
                    // TODO: calls that assign to destinations?
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
        data: FunctionData,
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
        let _conditionals = self.collect_conditionals(&target, &cfg);

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
