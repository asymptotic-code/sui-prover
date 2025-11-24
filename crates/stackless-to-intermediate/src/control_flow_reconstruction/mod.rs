// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control flow reconstruction module
//!
//! Directly reconstructs CFG to Statement IR with three phases:
//! 1. Structure Discovery: Identify if/else/while patterns
//! 2. Termination Handling: Identify terminating branches
//! 3. Phi-Node Computation: Compute phi-variables using dominance frontiers
//!
//! No intermediate StructuredBlock phase - builds Statement IR directly.

use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::VariableRegistry;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::graph::DomRelation;
use move_stackless_bytecode::stackless_bytecode::Bytecode;
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};

mod helpers;
mod structure_discovery;
pub mod phi_computation;
mod loop_substitution;
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
        let forward_cfg = StacklessControlFlowGraph::new_forward(code);
        let back_cfg = StacklessControlFlowGraph::new_backward(code, true);

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
        use move_stackless_bytecode::graph::Graph;

        let entry = cfg.entry_block();
        let nodes = cfg.blocks();

        // Build edges list
        let mut edges = Vec::new();
        for &block in &nodes {
            for &succ in cfg.successors(block) {
                edges.push((block, succ));
            }
        }

        let graph = Graph::new(entry, nodes, edges);
        DomRelation::new(&graph)
    }
}
