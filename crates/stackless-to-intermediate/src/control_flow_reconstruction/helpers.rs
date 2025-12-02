// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Helper functions for control flow reconstruction

use super::DiscoveryContext;
use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::{
    BlockContent, BlockId, StacklessControlFlowGraph,
};

pub fn block_bounds(cfg: &StacklessControlFlowGraph, block: BlockId) -> Option<(CodeOffset, CodeOffset)> {
    match cfg.content(block) {
        BlockContent::Basic { lower, upper } => Some((*lower, *upper)),
        _ => None,
    }
}

pub fn resolve_label_block(ctx: &DiscoveryContext, label: Label) -> Option<BlockId> {
    let code = ctx.target.get_bytecode();
    let target_pc = (0..code.len()).find(|&offset| {
        matches!(&code[offset], Bytecode::Label(_, found) if found == &label)
    })?;
    StacklessControlFlowGraph::pc_to_block(&ctx.forward_cfg, target_pc as u16)
}
