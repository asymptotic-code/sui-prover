// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Formal dominance analysis and phi-node placement using dominance frontiers.
//!
//! This module implements the classic SSA construction algorithm:
//! - Compute dominance tree using iterative dataflow
//! - Compute dominance frontiers from the dominance tree
//! - Place phi-nodes at dominance frontiers of variable definitions
//!
//! Based on "Efficiently Computing Static Single Assignment Form" (Cytron et al., 1991)

use crate::stackless_bytecode::Bytecode;
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Information about where phi-nodes are needed
#[derive(Debug, Clone)]
pub struct PhiPlacement {
    /// Map from block ID to set of variables that need phi-nodes at that block
    pub phi_blocks: BTreeMap<BlockId, BTreeSet<usize>>,
}

impl PhiPlacement {
    /// Compute phi-node placement for all variables in the function
    pub fn compute(code: &[Bytecode], cfg: &StacklessControlFlowGraph) -> Self {
        let mut analyzer = DominanceAnalyzer::new(code, cfg);
        analyzer.compute_dominators();
        analyzer.compute_dominance_frontiers();
        analyzer.collect_variable_definitions();
        analyzer.place_phi_functions();

        PhiPlacement {
            phi_blocks: analyzer.phi_blocks,
        }
    }

    /// Check if a variable needs a phi-node at a given block
    pub fn needs_phi(&self, block: BlockId, variable: usize) -> bool {
        self.phi_blocks
            .get(&block)
            .map_or(false, |vars| vars.contains(&variable))
    }

    /// Get all variables that need phi-nodes at a block
    pub fn get_phi_variables(&self, block: BlockId) -> Option<&BTreeSet<usize>> {
        self.phi_blocks.get(&block)
    }
}

/// Internal analyzer for computing dominance and phi-placement
struct DominanceAnalyzer<'a> {
    code: &'a [Bytecode],
    cfg: &'a StacklessControlFlowGraph,
    /// Predecessors map (computed from CFG)
    predecessors: BTreeMap<BlockId, Vec<BlockId>>,
    /// Immediate dominators (block -> idom)
    idom: BTreeMap<BlockId, BlockId>,
    /// Dominance frontiers (block -> set of blocks in DF)
    df: BTreeMap<BlockId, BTreeSet<BlockId>>,
    /// Variables defined in each block
    var_defs: BTreeMap<BlockId, BTreeSet<usize>>,
    /// Blocks where each variable needs a phi-node
    phi_blocks: BTreeMap<BlockId, BTreeSet<usize>>,
}

impl<'a> DominanceAnalyzer<'a> {
    fn new(code: &'a [Bytecode], cfg: &'a StacklessControlFlowGraph) -> Self {
        // Build predecessors map
        let mut predecessors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        for block in cfg.blocks() {
            for &succ in cfg.successors(block) {
                predecessors.entry(succ).or_default().push(block);
            }
        }

        Self {
            code,
            cfg,
            predecessors,
            idom: BTreeMap::new(),
            df: BTreeMap::new(),
            var_defs: BTreeMap::new(),
            phi_blocks: BTreeMap::new(),
        }
    }

    /// Compute immediate dominators using iterative dataflow analysis
    fn compute_dominators(&mut self) {
        let entry = self.cfg.entry_block();
        let blocks: Vec<BlockId> = self.cfg.blocks();

        // Initialize: entry dominates itself
        self.idom.insert(entry, entry);

        // Iterate until fixed point
        let mut changed = true;
        while changed {
            changed = false;

            for &block in &blocks {
                if block == entry {
                    continue;
                }

                // Get predecessors
                let preds = self.predecessors.get(&block)
                    .map(|v| v.as_slice())
                    .unwrap_or(&[]);

                if preds.is_empty() {
                    continue;
                }

                // Find new idom as intersection of predecessors' dominators
                let mut new_idom = None;
                for &pred in preds {
                    if let Some(&pred_dom) = self.idom.get(&pred) {
                        new_idom = Some(match new_idom {
                            None => pred_dom,
                            Some(current) => self.intersect(pred_dom, current),
                        });
                    }
                }

                if let Some(new_idom) = new_idom {
                    if self.idom.get(&block) != Some(&new_idom) {
                        self.idom.insert(block, new_idom);
                        changed = true;
                    }
                }
            }
        }
    }

    /// Find common dominator of two blocks (helper for dominance computation)
    fn intersect(&self, mut b1: BlockId, mut b2: BlockId) -> BlockId {
        while b1 != b2 {
            while b1 > b2 {
                if let Some(&idom) = self.idom.get(&b1) {
                    b1 = idom;
                } else {
                    return b2;
                }
            }
            while b2 > b1 {
                if let Some(&idom) = self.idom.get(&b2) {
                    b2 = idom;
                } else {
                    return b1;
                }
            }
        }
        b1
    }

    /// Compute dominance frontiers using dominance tree
    fn compute_dominance_frontiers(&mut self) {
        let blocks: Vec<BlockId> = self.cfg.blocks();

        for &block in &blocks {
            let preds = self.predecessors.get(&block)
                .map(|v| v.as_slice())
                .unwrap_or(&[]);

            // Blocks with multiple predecessors are candidates for DF
            if preds.len() >= 2 {
                for &pred in preds {
                    let mut runner = pred;

                    // Walk up dominance tree until we find block's idom
                    let block_idom = self.idom.get(&block).copied().unwrap_or(runner);
                    while runner != block_idom {
                        self.df.entry(runner).or_default().insert(block);

                        if let Some(&idom) = self.idom.get(&runner) {
                            if idom == runner {
                                break; // Reached root
                            }
                            runner = idom;
                        } else {
                            break;
                        }
                    }
                }
            }
        }
    }

    /// Collect which variables are defined in each block
    fn collect_variable_definitions(&mut self) {
        for block_id in self.cfg.blocks() {
            let block_content = self.cfg.content(block_id);
            let mut vars = BTreeSet::new();

            if let BlockContent::Basic { lower, upper } = block_content {
                for pc in *lower..=*upper {
                    if let Some(bc) = self.code.get(pc as usize) {
                        match bc {
                            Bytecode::Assign(_, dst, _, _) |
                            Bytecode::Load(_, dst, _) => {
                                vars.insert(*dst);
                            }
                            Bytecode::Call(_, dests, _, _, _) => {
                                vars.extend(dests);
                            }
                            _ => {}
                        }
                    }
                }
            }

            self.var_defs.insert(block_id, vars);
        }
    }

    /// Place phi-functions at dominance frontiers using worklist algorithm
    fn place_phi_functions(&mut self) {
        // Find all variables that are ever defined
        let all_vars: BTreeSet<usize> = self.var_defs.values()
            .flat_map(|vars| vars.iter())
            .copied()
            .collect();

        for var in all_vars {
            // Find all blocks that define this variable
            let mut def_blocks = BTreeSet::new();
            for (block, vars) in &self.var_defs {
                if vars.contains(&var) {
                    def_blocks.insert(*block);
                }
            }

            // Place phi-functions at dominance frontiers using worklist
            let mut worklist: VecDeque<BlockId> = def_blocks.iter().copied().collect();
            let mut phi_placed = BTreeSet::new();

            while let Some(block) = worklist.pop_front() {
                if let Some(df_blocks) = self.df.get(&block) {
                    for &df_block in df_blocks {
                        if phi_placed.contains(&df_block) {
                            continue;
                        }

                        // Place phi-function for var at df_block
                        phi_placed.insert(df_block);
                        self.phi_blocks.entry(df_block).or_default().insert(var);

                        // If df_block didn't define var before, add to worklist
                        if !def_blocks.contains(&df_block) {
                            def_blocks.insert(df_block);
                            worklist.push_back(df_block);
                        }
                    }
                }
            }
        }
    }
}
