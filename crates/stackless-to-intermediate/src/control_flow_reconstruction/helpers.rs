// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Helper functions for control flow reconstruction

use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::{
    BlockContent, BlockId, StacklessControlFlowGraph,
};

use crate::control_flow_reconstruction::DiscoveryContext;

/// Get block bounds (lower, upper) code offsets
pub fn block_bounds(
    cfg: &StacklessControlFlowGraph,
    block: BlockId,
) -> Option<(CodeOffset, CodeOffset)> {
    match cfg.content(block) {
        BlockContent::Basic { lower, upper } => Some((*lower, *upper)),
        _ => None,
    }
}

/// Resolve label to block ID
pub fn resolve_label_block(ctx: &mut DiscoveryContext, label: Label) -> Option<BlockId> {
    let target_pc = (0..ctx.code.len()).find(|&offset| {
        if let Bytecode::Label(_, found) = &ctx.code[offset] {
            *found == label
        } else {
            false
        }
    })?;
    
    StacklessControlFlowGraph::pc_to_block(&ctx.forward_cfg, target_pc as u16)
}