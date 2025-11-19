// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0
use move_binary_format::file_format::CodeOffset;
use crate::stackless_bytecode::Bytecode;
use crate::graph::NaturalLoop;
use crate::ast::TempIndex;

/// Represents a phi-node for a loop-carried variable.
/// In SSA form, loop-carried variables need phi-nodes to merge values
/// from the loop entry (initial value) and loop back-edge (updated value).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopPhiVariable {
    /// The temporary variable index that is loop-carried
    pub temp: usize,

    /// The temporary holding the initial value before entering the loop
    pub initial_value: usize,

    /// The temporary holding the updated value from the loop body (computed after body execution)
    pub updated_value: usize,
}

impl LoopPhiVariable {
    pub fn new(temp: usize, initial_value: usize, updated_value: usize) -> Self {
        Self {
            temp,
            initial_value,
            updated_value,
        }
    }
}

/// Represents a phi-node for an if/else merge point.
/// In SSA form, variables that have different values from each branch
/// need phi-nodes to merge at the join point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IfPhiVariable {
    /// The temporary variable index that has different values in branches
    pub temp: usize,

    /// The temporary holding the value from the then branch
    pub then_value: usize,

    /// The temporary holding the value from the else branch (or before-if value if no else)
    pub else_value: usize,
}

impl IfPhiVariable {
    pub fn new(temp: usize, then_value: usize, else_value: usize) -> Self {
        Self {
            temp,
            then_value,
            else_value,
        }
    }
}

/// A BasicBlock with a tree structure for control flow
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuredBlock {
    /// A straight-line sequence of bytecodes from `lower..=upper` (inclusive)
    Basic { lower: CodeOffset, upper: CodeOffset },

    /// A sequence of blocks
    Seq(Vec<StructuredBlock>),

    /// A structured if/else with the condition temp extracted from the Branch instruction.
    /// `cond_at` is the bytecode offset (used for loop detection during CFG reconstruction).
    /// `cond_temp` is the temp index (used for IR translation, avoids bytecode lookups).
    /// `else_branch` is None for if-then.
    /// `phi_variables` contains temps that have different values from each branch.
    IfThenElse {
        cond_at: CodeOffset,
        cond_temp: TempIndex,
        then_branch: Box<StructuredBlock>,
        else_branch: Option<Box<StructuredBlock>>,
        phi_variables: Vec<IfPhiVariable>,
    },

    /// A structured if/else-if/else chain with multiple conditions.
    /// Each entry in `branches` is ((offset, temp), body).
    /// The final `else_branch` is optional.
    IfElseChain {
        branches: Vec<((CodeOffset, TempIndex), Box<StructuredBlock>)>,
        else_branch: Option<Box<StructuredBlock>>,
    },

    /// A while loop with condition temp extracted from the Branch instruction.
    /// `cond_at` is the bytecode offset (used for loop detection during CFG reconstruction).
    /// `cond_temp` is the temp index (used for IR translation, avoids bytecode lookups).
    /// The condition is checked before each iteration (while semantics, not do-while).
    /// `condition_body` contains the bytecode that computes the condition value (from header to branch).
    /// `phi_variables` contains loop-carried variables with their phi-nodes.
    While {
        cond_at: CodeOffset,
        cond_temp: TempIndex,
        condition_body: Box<StructuredBlock>,
        body: Box<StructuredBlock>,
        phi_variables: Vec<LoopPhiVariable>,
    },
}

impl StructuredBlock {
    /// Iterate over bytecode offsets contained in this structured block, in order.
    pub fn iter_offsets<'a>(&'a self) -> Box<dyn Iterator<Item = CodeOffset> + 'a> {
        match self {
            StructuredBlock::Basic { lower, upper } => Box::new((*lower)..=(*upper)),
            StructuredBlock::Seq(blocks) => Box::new(blocks.iter().flat_map(|block| block.iter_offsets())),
            StructuredBlock::IfThenElse { then_branch, else_branch, phi_variables: _, .. } => {
                let then_iter = then_branch.iter_offsets();
                if let Some(else_block) = else_branch {
                    let else_iter = else_block.iter_offsets();
                    Box::new(then_iter.chain(else_iter))
                } else {
                    then_iter
                }
            }
            StructuredBlock::IfElseChain { branches, else_branch } => {
                let chain_iter = branches.iter().flat_map(|(_, body)| body.iter_offsets());
                if let Some(else_block) = else_branch {
                    let else_iter = else_block.iter_offsets();
                    Box::new(chain_iter.chain(else_iter))
                } else {
                    Box::new(chain_iter)
                }
            }
            StructuredBlock::While { condition_body, body, .. } => {
                let cond_iter = condition_body.iter_offsets();
                let body_iter = body.iter_offsets();
                Box::new(cond_iter.chain(body_iter))
            }
        }
    }

    /// Convert nested IfThenElse structures into an IfElseChain if they form a chain pattern.
    /// Preserves phi_variables if the structure doesn't form a chain.
    pub fn optimize_to_chain(self) -> Self {
        match self {
            StructuredBlock::IfThenElse { cond_at, cond_temp, then_branch, else_branch, phi_variables } => {
                Self::build_chain_from_if(cond_at, cond_temp, then_branch, else_branch, phi_variables)
            }
            other => other,
        }
    }

    /// Detect and convert IfThenElse with back-edges into While loops.
    /// Uses natural loop information from dominator analysis.
    pub fn detect_loops(self, code: &[Bytecode], natural_loops: &[NaturalLoop<CodeOffset>]) -> Self {
        match self {
            StructuredBlock::Seq(blocks) => {
                let optimized: Vec<StructuredBlock> = blocks.into_iter()
                    .map(|b| b.detect_loops(code, natural_loops))
                    .collect();
                StructuredBlock::Seq(optimized)
            }
            StructuredBlock::IfThenElse { cond_at, cond_temp, then_branch, else_branch, phi_variables } => {
                // Check if this branch creates a back-edge, indicating a loop
                let is_loop = Self::is_loop_back_edge(cond_at, code, natural_loops);

                if is_loop {

                    // This is a while loop: while (condition) { then_branch }
                    // The else_branch contains the continuation code (executed after loop exits)
                    // We need to return Seq([While, continuation]) to preserve the post-loop code

                    // Find the natural loop for this header
                    let loop_header_range = natural_loops.iter()
                        .find(|nl| nl.loop_header <= cond_at && cond_at <= nl.loop_header + 10)
                        .map(|nl| nl.loop_header);

                    let condition_body = if let Some(header_pc) = loop_header_range {
                        // Create a Basic block from header to cond_at
                        // This includes label and any condition computation
                        Box::new(StructuredBlock::Basic {
                            lower: header_pc,
                            upper: cond_at
                        })
                    } else {
                        // Fallback: just the branch instruction itself
                        Box::new(StructuredBlock::Basic {
                            lower: cond_at,
                            upper: cond_at
                        })
                    };

                    let while_loop = StructuredBlock::While {
                        cond_at,
                        cond_temp,
                        condition_body,
                        body: Box::new(then_branch.detect_loops(code, natural_loops)),
                        phi_variables: vec![],  // Phi-nodes will be computed in a later pass
                    };

                    // Include the else_branch as continuation code after the loop
                    match else_branch {
                        Some(continuation) => {
                            let processed_continuation = continuation.detect_loops(code, natural_loops);
                            // Return sequence: [while_loop, continuation]
                            StructuredBlock::Seq(vec![
                                while_loop,
                                processed_continuation
                            ])
                        }
                        None => {
                            while_loop
                        }
                    }
                } else {
                    // Regular if-then-else, recursively optimize branches
                    // PRESERVE phi_variables that were computed by dominance analysis
                    StructuredBlock::IfThenElse {
                        cond_at,
                        cond_temp,
                        then_branch: Box::new(then_branch.detect_loops(code, natural_loops)),
                        else_branch: else_branch.map(|b| Box::new(b.detect_loops(code, natural_loops))),
                        phi_variables,  // PRESERVE phi-variables from dominance analysis!
                    }
                }
            }
            StructuredBlock::IfElseChain { branches, else_branch } => {
                let optimized_branches: Vec<_> = branches.into_iter()
                    .map(|(cond, body)| (cond, Box::new(body.detect_loops(code, natural_loops))))
                    .collect();
                StructuredBlock::IfElseChain {
                    branches: optimized_branches,
                    else_branch: else_branch.map(|b| Box::new(b.detect_loops(code, natural_loops))),
                }
            }
            StructuredBlock::While { cond_at, cond_temp, condition_body, body, phi_variables } => {
                StructuredBlock::While {
                    cond_at,
                    cond_temp,
                    condition_body: Box::new(condition_body.detect_loops(code, natural_loops)),
                    body: Box::new(body.detect_loops(code, natural_loops)),
                    phi_variables,  // Preserve existing phi-variables
                }
            }
            other => other,
        }
    }

    /// Check if a branch at cond_at is actually a loop header
    /// This happens when the branch is part of a natural loop structure detected by CFG analysis
    fn is_loop_back_edge(cond_at: CodeOffset, code: &[Bytecode], natural_loops: &[NaturalLoop<CodeOffset>]) -> bool {
        // Get the branch instruction at cond_at
        if cond_at as usize >= code.len() {
            return false;
        }

        let instr = &code[cond_at as usize];

        // Get the branch destinations (labels)
        let labels = instr.branch_dests();
        if labels.is_empty() {
            return false;
        }

        // Build label->offset map
        let label_offsets = Bytecode::label_offsets(code);

        // Check if the branch itself is at a loop header (or just after it)
        // In Move bytecode, the loop header typically has the condition check,
        // and one branch goes into the loop body while the other exits the loop
        let mut target_offsets = vec![];
        for label in labels.iter() {
            if let Some(&target_offset) = label_offsets.get(label) {
                target_offsets.push(target_offset);
            }
        }

        let is_loop_header = natural_loops.iter().any(|nl| {
            // The branch is at a loop header if:
            // 1. The condition is at or just after the loop header instruction
            // 2. One of the targets goes forward (loop body or exit)
            // The loop header could be a Label instruction just before the condition
            let near_header = nl.loop_header <= cond_at && cond_at <= nl.loop_header + 10;
            near_header
        });

        is_loop_header
    }

    /// Build the chain from the inside of the IfThenElse by looping over every else that's found
    /// Preserves phi_variables if no chain is formed (branches.len() == 1)
    fn build_chain_from_if(
        first_cond_at: CodeOffset,
        first_cond_temp: TempIndex,
        first_then: Box<StructuredBlock>,
        mut current_else: Option<Box<StructuredBlock>>,
        phi_variables: Vec<super::types::IfPhiVariable>,
    ) -> Self {
        let mut branches: Vec<((CodeOffset, TempIndex), Box<StructuredBlock>)> = vec![((first_cond_at, first_cond_temp), first_then)];

        while let Some(else_block) = current_else {
            match *else_block {
                StructuredBlock::IfThenElse { cond_at, cond_temp, then_branch, else_branch, .. } => {
                    branches.push(((cond_at, cond_temp), then_branch));
                    current_else = else_branch;
                }
                StructuredBlock::Seq(blocks) => {
                    match Self::unwrap_seq_for_chain(blocks) {
                        SeqUnwrapResult::Advanced { next_cond_at, next_cond_temp, next_then, next_else } => {
                            branches.push(((next_cond_at, next_cond_temp), next_then));
                            current_else = next_else;
                        }
                        SeqUnwrapResult::NotChain(restored) => {
                            current_else = Some(Box::new(StructuredBlock::Seq(restored)));
                            break;
                        }
                    }
                }
                other => {
                    current_else = Some(Box::new(other));
                    break;
                }
            }
        }

        if branches.len() > 1 {
            // Formed a chain - no phi_variables on chains
            StructuredBlock::IfElseChain {
                branches,
                else_branch: current_else,
            }
        } else {
            // Not a chain - preserve the original if-statement with phi_variables
            let ((cond_at, cond_temp), then_branch) = branches.into_iter().next().unwrap();
            StructuredBlock::IfThenElse {
                cond_at,
                cond_temp,
                then_branch,
                else_branch: current_else,
                phi_variables,  // PRESERVE phi-variables from dominance analysis!
            }
        }
    }

    /// Tries to unwrap a sequential block into a IfElseChain
    fn unwrap_seq_for_chain(mut blocks: Vec<StructuredBlock>) -> SeqUnwrapResult {
        // Pattern 1: Single IfThenElse inside the Seq
        if blocks.len() == 1 {
            let single = blocks.pop().unwrap();
            if let StructuredBlock::IfThenElse { cond_at, cond_temp, then_branch, else_branch, .. } = single {
                return SeqUnwrapResult::Advanced {
                    next_cond_at: cond_at,
                    next_cond_temp: cond_temp,
                    next_then: then_branch,
                    next_else: else_branch,
                };
            }
            return SeqUnwrapResult::NotChain(vec![single]);
        }

        // Pattern 2: [IfThenElse, ...rest] with optional prefix not allowed
        let if_index = blocks
            .iter()
            .position(|b| matches!(b, StructuredBlock::IfThenElse { .. }));

        let Some(idx) = if_index else {
            return SeqUnwrapResult::NotChain(blocks);
        };

        if idx != 0 {
            return SeqUnwrapResult::NotChain(blocks);
        }

        // Extract the IfThenElse and the remaining tail
        let mut remaining = blocks.split_off(idx);
        let if_block = remaining.remove(0);

        if let StructuredBlock::IfThenElse { cond_at, cond_temp, then_branch, mut else_branch, .. } = if_block {
            if !remaining.is_empty() {
                if let Some(else_content) = else_branch.take() {
                    remaining.insert(0, *else_content);
                }
                else_branch = Some(Box::new(StructuredBlock::Seq(remaining)));
            }

            return SeqUnwrapResult::Advanced {
                next_cond_at: cond_at,
                next_cond_temp: cond_temp,
                next_then: then_branch,
                next_else: else_branch,
            };
        }

        // Should not reach here; restore original and report NotChain
        SeqUnwrapResult::NotChain({
            let mut restored = blocks;
            restored.extend(remaining);
            restored.insert(idx, if_block);
            restored
        })
    }
}

/// The result of unwrapping a sequential block
enum SeqUnwrapResult {
    /// An IfElseChain was found, giving the information on the next part
    Advanced {
        next_cond_at: CodeOffset,
        next_cond_temp: TempIndex,
        next_then: Box<StructuredBlock>,
        next_else: Option<Box<StructuredBlock>>,
    },
    /// No chain
    NotChain(Vec<StructuredBlock>),
}
