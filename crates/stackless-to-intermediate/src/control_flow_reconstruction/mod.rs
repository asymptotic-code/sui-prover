// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control flow reconstruction module
//!
//! Reconstructs CFG to Statement IR with expression-based control flow:
//! - If/While are expressions (IfExpr, WhileExpr) that produce values
//! - No separate phi/loop variable tracking - values flow through expression results
//! - Single-pass structure discovery builds the complete IR

use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::VariableRegistry;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::graph::{DomRelation, Graph};
use move_stackless_bytecode::stackless_bytecode::Bytecode;
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};

mod helpers;
mod structure_discovery;
mod reconstructor;

pub use reconstructor::reconstruct_and_translate;

/// Context for structure discovery
pub struct DiscoveryContext<'a, 'b, 'c> {
    pub code: &'a [Bytecode],
    pub builder: &'a mut ProgramBuilder<'b>,
    pub target: &'a FunctionTarget<'c>,
    pub registry: &'a mut VariableRegistry,
    pub forward_dom: DomRelation<BlockId>,
    pub back_dom: DomRelation<BlockId>,
    pub forward_cfg: StacklessControlFlowGraph,
    pub back_cfg: StacklessControlFlowGraph,
}

impl<'a, 'b, 'c> DiscoveryContext<'a, 'b, 'c> {
    pub fn new(code: &'a [Bytecode],
               builder: &'a mut ProgramBuilder<'b>,
               target: &'a FunctionTarget<'c>,
               registry: &'a mut VariableRegistry) -> Self {
        let forward_cfg = StacklessControlFlowGraph::new_forward_with_options(code, true);
        let back_cfg = StacklessControlFlowGraph::new_backward_with_options(code, false, true);
        
        // Build dominator relations from CFGs
        let forward_dom = Self::build_dominator_relation(&forward_cfg);
        let back_dom = Self::build_dominator_relation(&back_cfg);
        
        Self {
            code,
            builder,
            target,
            registry,
            forward_dom,
            back_dom,
            forward_cfg,
            back_cfg,
        }
    }
    
    /// Build a dominator relation from a control flow graph
    fn build_dominator_relation(cfg: &StacklessControlFlowGraph) -> DomRelation<BlockId> {
        let entry = cfg.entry_block();
        let nodes = cfg.blocks();
        
        // Build edges list
        let edges = nodes.iter()
            .flat_map(|block|
                cfg.successors(*block).iter().map(|succ| (*block, *succ)))
            .collect::<Vec<_>>();
        
        let graph = Graph::new(entry, nodes, edges);
        DomRelation::new(&graph)
    }
}
