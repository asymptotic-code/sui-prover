// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

//! Adapted from control_flow_graph for Bytecode, this module defines the control-flow graph on
//! Stackless Bytecode used in analysis as part of Move prover.

use crate::{
    function_target::FunctionTarget,
    stackless_bytecode::{Bytecode, Label},
};
use move_binary_format::file_format::CodeOffset;
use petgraph::{
    algo::{self, dominators},
    dot::Dot,
    graph::{self, DiGraph, Graph},
};
use std::collections::{BTreeMap, BTreeSet};

type Map<K, V> = BTreeMap<K, V>;
type Set<V> = BTreeSet<V>;
pub type BlockId = CodeOffset;

#[derive(Debug)]
struct Block {
    successors: Vec<BlockId>,
    content: BlockContent,
}

#[derive(Copy, Clone, Debug)]
pub enum BlockContent {
    Basic {
        lower: CodeOffset,
        upper: CodeOffset,
    },
    Dummy,
}

pub struct StacklessControlFlowGraph {
    entry_block_id: BlockId,
    blocks: Map<BlockId, Block>,
    backward: bool,
    ignore_return_abort: bool,
}

const DUMMY_ENTRANCE: BlockId = 0;
const DUMMY_EXIT: BlockId = 1;

impl StacklessControlFlowGraph {
    pub fn new_forward(code: &[Bytecode]) -> Self {
        Self::new_forward_with_options(code, false)
    }

    pub fn new_forward_with_options(code: &[Bytecode], ignore_return_abort: bool) -> Self {
        Self {
            entry_block_id: DUMMY_ENTRANCE,
            blocks: Self::collect_blocks(code, ignore_return_abort),
            backward: false,
            ignore_return_abort,
        }
    }

    /// If from_all_blocks is false, perform backward analysis only from blocks that may exit.
    /// If from_all_blocks is true, perform backward analysis from all blocks.
    pub fn new_backward(code: &[Bytecode], from_all_blocks: bool) -> Self {
        Self::new_backward_with_options(code, from_all_blocks, false)
    }

    pub fn new_backward_with_options(
        code: &[Bytecode],
        from_all_blocks: bool,
        ignore_return_abort: bool,
    ) -> Self {
        let blocks = Self::collect_blocks(code, ignore_return_abort);
        let mut block_id_to_predecessors: Map<BlockId, Vec<BlockId>> =
            blocks.keys().map(|block_id| (*block_id, vec![])).collect();
        for (block_id, block) in &blocks {
            for succ_block_id in &block.successors {
                if from_all_blocks && *succ_block_id == DUMMY_EXIT {
                    continue;
                }
                let predecessors = &mut block_id_to_predecessors.get_mut(succ_block_id).unwrap();
                predecessors.push(*block_id);
            }
        }
        if from_all_blocks {
            let predecessors = &mut block_id_to_predecessors.get_mut(&DUMMY_EXIT).unwrap();
            blocks.keys().for_each(|block_id| {
                if *block_id != DUMMY_ENTRANCE && *block_id != DUMMY_EXIT {
                    predecessors.push(*block_id);
                }
            });
        }
        Self {
            entry_block_id: DUMMY_EXIT,
            blocks: block_id_to_predecessors
                .into_iter()
                .map(|(block_id, predecessors)| {
                    (
                        block_id,
                        Block {
                            successors: predecessors,
                            content: blocks[&block_id].content,
                        },
                    )
                })
                .collect(),
            backward: true,
            ignore_return_abort,
        }
    }

    /// Generate a block that contains all the code
    pub fn one_block(code: &[Bytecode]) -> Self {
        let mut blocks = Map::new();
        let mut successors = vec![];
        let entry_bb = 2 as BlockId;
        successors.insert(0, entry_bb);
        successors.insert(1, DUMMY_EXIT);
        let bb = BlockContent::Basic {
            lower: 0,
            upper: code.len() as u16 - 1,
        };
        blocks.insert(
            entry_bb,
            Block {
                successors,
                content: bb,
            },
        );
        blocks.insert(
            DUMMY_ENTRANCE,
            Block {
                successors: vec![entry_bb],
                content: BlockContent::Dummy,
            },
        );
        blocks.insert(
            DUMMY_EXIT,
            Block {
                successors: Vec::new(),
                content: BlockContent::Dummy,
            },
        );
        Self {
            entry_block_id: DUMMY_ENTRANCE,
            blocks,
            backward: false,
            ignore_return_abort: false,
        }
    }

    fn collect_blocks(code: &[Bytecode], ignore_return_abort: bool) -> Map<BlockId, Block> {
        assert!(code.len() > 0);
        // First go through and collect basic block offsets.
        // Need to do this first in order to handle backwards edges.
        let label_offsets = Bytecode::label_offsets(code);
        let mut bb_offsets = Set::new();
        bb_offsets.insert(0);
        for pc in 0..code.len() {
            StacklessControlFlowGraph::record_block_ids(
                pc as CodeOffset,
                code,
                &mut bb_offsets,
                &label_offsets,
                ignore_return_abort,
            );
        }
        // Now construct blocks
        let mut blocks = Map::new();
        // Maps basic block entry offsets to their key in blocks
        let mut offset_to_key = Map::new();
        let mut block_entry = 0;
        for pc in 0..code.len() {
            let co_pc: CodeOffset = pc as CodeOffset;
            // Create a basic block
            if StacklessControlFlowGraph::is_end_of_block(co_pc, code, &bb_offsets) {
                let mut successors = Bytecode::get_successors(co_pc, code, &label_offsets);
                for successor in successors.iter_mut() {
                    *successor = Self::get_block_id(&mut offset_to_key, *successor);
                }
                if !ignore_return_abort {
                    if code[pc].is_exit() || matches!(code[pc], Bytecode::Call(_, _, _, _, Some(_)))
                    {
                        successors.push(DUMMY_EXIT);
                    }
                } else {
                    assert_eq!(
                        code[pc].is_exit() || pc + 1 == code.len(),
                        successors.is_empty(),
                        "code[{}]: {:?}",
                        pc,
                        code[pc]
                    );
                    if pc + 1 == code.len() {
                        assert!(code[pc].is_exit() || !code[pc].is_branch());
                        successors.push(DUMMY_EXIT);
                    } else if code[pc].is_exit() {
                        successors.push(Self::get_block_id(&mut offset_to_key, co_pc + 1));
                    }
                }
                let bb = BlockContent::Basic {
                    lower: block_entry,
                    upper: co_pc,
                };
                let key = Self::get_block_id(&mut offset_to_key, block_entry);
                blocks.insert(
                    key,
                    Block {
                        successors,
                        content: bb,
                    },
                );
                block_entry = co_pc + 1;
            }
        }
        assert_eq!(block_entry, code.len() as CodeOffset);
        let entry_bb = *offset_to_key.get(&0).unwrap();
        blocks.insert(
            DUMMY_ENTRANCE,
            Block {
                successors: vec![entry_bb],
                content: BlockContent::Dummy,
            },
        );
        blocks.insert(
            DUMMY_EXIT,
            Block {
                successors: Vec::new(),
                content: BlockContent::Dummy,
            },
        );
        blocks
    }

    fn get_block_id(offset_to_key: &mut Map<CodeOffset, BlockId>, offset: CodeOffset) -> BlockId {
        // block counter starts at 2 because entry and exit will be block 0 and 1,
        // so the next block id is the length of the map plus 2.
        let next_block_id = (offset_to_key.len() + 2) as BlockId;
        *offset_to_key.entry(offset).or_insert(next_block_id)
    }

    fn is_end_of_block(pc: CodeOffset, code: &[Bytecode], block_ids: &Set<BlockId>) -> bool {
        pc + 1 == (code.len() as CodeOffset) || block_ids.contains(&(pc + 1))
    }

    fn record_block_ids(
        pc: CodeOffset,
        code: &[Bytecode],
        block_ids: &mut Set<BlockId>,
        label_offsets: &BTreeMap<Label, CodeOffset>,
        ignore_aborts: bool,
    ) {
        let bytecode = &code[pc as usize];

        for label in bytecode.branch_dests() {
            block_ids.insert(*label_offsets.get(&label).unwrap());
        }

        if !ignore_aborts && matches!(bytecode, Bytecode::Call(_, _, _, _, Some(_))) {
            block_ids.insert(pc + 1);
        }
    }

    pub fn block_start_pc(cfg: &StacklessControlFlowGraph, block: BlockId) -> Option<u16> {
        match cfg.content(block) {
            BlockContent::Basic { lower, .. } => Some(*lower),
            BlockContent::Dummy => None,
        }
    }

    pub fn pc_to_block(cfg: &StacklessControlFlowGraph, pc: u16) -> Option<BlockId> {
        for b in cfg.blocks() {
            match cfg.content(b) {
                BlockContent::Basic { lower, upper } => {
                    if *lower <= pc && pc <= *upper {
                        return Some(b);
                    }
                }
                BlockContent::Dummy => {}
            }
        }
        None
    }

    pub fn find_immediate_dominator(
        self: &StacklessControlFlowGraph,
        branch_block: BlockId,
    ) -> Option<BlockId> {
        // Compute dominators using petgraph (on backward CFG this gives post-dominators)
        let (graph, block_to_node) = self.as_directed_graph();
        let dominators = dominators::simple_fast(&graph, block_to_node[&self.entry_block()]);

        // Get immediate dominator of branch_block
        dominators
            .immediate_dominator(block_to_node[&branch_block])
            .map(|idom_node| graph[idom_node])
    }

    pub fn as_directed_graph(&self) -> (DiGraph<BlockId, ()>, BTreeMap<BlockId, graph::NodeIndex>) {
        // Build petgraph DiGraph and create mappings between BlockId and NodeIndex
        let mut graph: DiGraph<BlockId, ()> = DiGraph::new();
        let mut block_to_node: BTreeMap<BlockId, graph::NodeIndex> = BTreeMap::new();

        // Add nodes
        for block_id in self.blocks() {
            let node_index = graph.add_node(block_id);
            block_to_node.insert(block_id, node_index);
        }

        // Add edges
        for block_id in self.blocks() {
            let from_node = block_to_node[&block_id];
            for succ in self.successors(block_id) {
                let to_node = block_to_node[succ];
                graph.add_edge(from_node, to_node, ());
            }
        }

        (graph, block_to_node)
    }

    pub fn is_acyclic(&self) -> bool {
        let (graph, _) = self.as_directed_graph();
        !algo::is_cyclic_directed(&graph)
    }

    pub fn successors(&self, block_id: BlockId) -> &Vec<BlockId> {
        &self.blocks[&block_id].successors
    }

    pub fn content(&self, block_id: BlockId) -> &BlockContent {
        &self.blocks[&block_id].content
    }

    pub fn blocks(&self) -> Vec<BlockId> {
        self.blocks.keys().cloned().collect()
    }

    pub fn entry_block(&self) -> BlockId {
        self.entry_block_id
    }

    pub fn exit_block(&self) -> BlockId {
        if self.backward {
            DUMMY_ENTRANCE
        } else {
            DUMMY_EXIT
        }
    }

    pub fn instr_indexes(
        &self,
        block_id: BlockId,
    ) -> Option<Box<dyn DoubleEndedIterator<Item = CodeOffset>>> {
        match self.blocks[&block_id].content {
            BlockContent::Basic { lower, upper } => Some(Box::new(lower..=upper)),
            BlockContent::Dummy => None,
        }
    }

    pub fn num_blocks(&self) -> u16 {
        self.blocks.len() as u16
    }

    pub fn is_dummmy(&self, block_id: BlockId) -> bool {
        matches!(self.blocks[&block_id].content, BlockContent::Dummy)
    }

    pub fn display(&self) {
        println!("+=======================+");
        println!("entry_block_id = {}", self.entry_block_id);
        println!("blocks = {:?}", self.blocks);
        println!("is_backward = {}", self.backward);
        println!("+=======================+");
    }
}

// CFG dot graph generation
struct DotCFGBlock<'env> {
    block_id: BlockId,
    content: BlockContent,
    func_target: &'env FunctionTarget<'env>,
    label_offsets: BTreeMap<Label, CodeOffset>,
}

impl std::fmt::Display for DotCFGBlock<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let code_range = match self.content {
            BlockContent::Basic { lower, upper } => format!("offset {}..={}", lower, upper),
            BlockContent::Dummy => "X".to_owned(),
        };
        writeln!(f, "[Block {} - {}]", self.block_id, code_range)?;
        match self.content {
            BlockContent::Basic { lower, upper } => {
                let code = &self.func_target.data.code;
                for (offset, instruction) in
                    (lower..=upper).zip(&code[(lower as usize)..=(upper as usize)])
                {
                    let text = self.func_target.pretty_print_bytecode(
                        &self.label_offsets,
                        offset as usize,
                        instruction,
                    );
                    writeln!(f, "{}", text)?;
                }
            }
            BlockContent::Dummy => {}
        }
        Ok(())
    }
}

// A dummy struct to implement fmt required by petgraph::Dot
struct DotCFGEdge {}

impl std::fmt::Display for DotCFGEdge {
    fn fmt(&self, _f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Ok(())
    }
}

/// Generate the dot representation of the CFG (which can be rendered by the Dot program)
pub fn generate_cfg_in_dot_format<'env>(func_target: &'env FunctionTarget<'env>) -> String {
    let code = &func_target.data.code;
    let cfg = StacklessControlFlowGraph::new_forward(code);
    let label_offsets = Bytecode::label_offsets(code);
    let mut graph = Graph::new();

    // add nodes
    let mut node_map = Map::new();
    for (block_id, block) in &cfg.blocks {
        let dot_block = DotCFGBlock {
            block_id: *block_id,
            content: block.content,
            func_target,
            label_offsets: label_offsets.clone(),
        };
        let node_index = graph.add_node(dot_block);
        node_map.insert(block_id, node_index);
    }

    // add edges
    for (block_id, block) in &cfg.blocks {
        for successor in &block.successors {
            graph.add_edge(
                *node_map.get(block_id).unwrap(),
                *node_map.get(successor).unwrap(),
                DotCFGEdge {},
            );
        }
    }

    // generate dot string
    format!(
        "{}",
        Dot::with_attr_getters(&graph, &[], &|_, _| "".to_string(), &|_, _| {
            "shape=box".to_string()
        })
    )
}
