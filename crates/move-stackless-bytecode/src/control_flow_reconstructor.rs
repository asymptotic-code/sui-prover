// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! A lightweight control-flow reconstructor that produces a structured sequence of
//! control blocks from stackless bytecode basic blocks. This is an initial version
//! which linearizes reachable basic blocks in a deterministic traversal order. It
//! provides an API surface that can later be extended to detect structured
//! conditionals and loops.

use crate::stackless_bytecode::{Bytecode};
use crate::stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph};
use move_binary_format::file_format::CodeOffset;
use std::collections::{BTreeSet, VecDeque};

#[derive(Clone, Debug)]
pub enum StructuredBlock {
    /// A straight-line sequence of bytecodes from `lower..=upper` (inclusive)
    Basic { lower: CodeOffset, upper: CodeOffset },
    /// A sequence of blocks
    Seq(Vec<StructuredBlock>),
    // Future: IfThenElse { cond_at: CodeOffset, then_branch: Box<StructuredBlock>, else_branch: Option<Box<StructuredBlock>> },
    // Future: Loop { header: BlockId, body: Box<StructuredBlock> },
}

impl StructuredBlock {
    /// Iterate over bytecode offsets contained in this structured block, in order.
    pub fn instr_indexes<'a>(&'a self) -> Box<dyn Iterator<Item = CodeOffset> + 'a> {
        match self {
            StructuredBlock::Basic { lower, upper } => Box::new((*lower)..=(*upper)),
            StructuredBlock::Seq(blocks) => Box::new(blocks.iter().flat_map(|b| b.instr_indexes())),
        }
    }
}

/// Reconstructs control flow from basic blocks into a structured representation.
///
/// Current strategy: reachability-preserving linearization via BFS from the entry
/// block over the existing CFG. Dummy entry/exit nodes are skipped.
pub fn reconstruct_control_flow(code: &[Bytecode]) -> Vec<StructuredBlock> {
    let cfg = StacklessControlFlowGraph::new_forward(code);
    let mut ordered: Vec<StructuredBlock> = Vec::new();

    let mut visited: BTreeSet<BlockId> = BTreeSet::new();
    let mut worklist: VecDeque<BlockId> = VecDeque::new();

    worklist.push_back(cfg.entry_block());

    while let Some(b) = worklist.pop_front() {
        if visited.contains(&b) {
            continue;
        }
        if cfg.is_dummmy(b) {
            // Do not skip over graph traversal at dummy nodes: enqueue their successors.
            for succ in cfg.successors(b) {
                if !visited.contains(succ) {
                    worklist.push_back(*succ);
                }
            }
            continue;
        }
        visited.insert(b);

        if let Some(range) = cfg.instr_indexes(b) {
            // Convert the basic block to a StructuredBlock::Basic
            let mut lower: Option<CodeOffset> = None;
            let mut upper: CodeOffset = 0;
            for idx in range {
                if lower.is_none() {
                    lower = Some(idx);
                }
                upper = idx;
            }
            if let Some(l) = lower {
                ordered.push(StructuredBlock::Basic { lower: l, upper });
            }
        }

        for succ in cfg.successors(b) {
            if !visited.contains(succ) {
                worklist.push_back(*succ);
            }
        }
    }

    ordered
}
