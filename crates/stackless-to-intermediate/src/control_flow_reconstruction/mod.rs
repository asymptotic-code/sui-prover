// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control flow reconstruction module

use crate::program_builder::ProgramBuilder;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::graph::DomRelation;
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};
use std::collections::BTreeMap;

mod helpers;
pub mod phi_detection;
pub mod structure_discovery;

pub struct DiscoveryContext<'a, 'b> {
    pub builder: &'a mut ProgramBuilder<'b>,
    pub target: FunctionTarget<'a>,
    pub forward_dom: DomRelation<BlockId>,
    pub forward_cfg: StacklessControlFlowGraph,
    /// Map from temp index to traced variable name (from TraceLocal operations)
    pub trace_names: BTreeMap<usize, String>,
}
