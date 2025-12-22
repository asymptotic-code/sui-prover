// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0
use move_binary_format::file_format::CodeOffset;

/// A BasicBlock with a tree structure for control flow
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StructuredBlock {
    /// A straight-line sequence of bytecodes from `lower..=upper` (inclusive)
    Basic {
        lower: CodeOffset,
        upper: CodeOffset,
    },

    /// A sequence of blocks
    Seq(Vec<StructuredBlock>),

    /// A structured if/else with the condition evaluated at `cond_at` (the Branch instruction)
    /// and structured bodies up to the merge point. `else_branch` is None for if-then.
    IfThenElse {
        cond_at: CodeOffset,
        then_branch: Box<StructuredBlock>,
        else_branch: Option<Box<StructuredBlock>>,
    },

    /// A structured if/else-if/else chain with multiple conditions.
    /// Each entry in `branches` is (condition_location, body).
    /// The final `else_branch` is optional.
    IfElseChain {
        branches: Vec<(CodeOffset, Box<StructuredBlock>)>,
        else_branch: Option<Box<StructuredBlock>>,
    },
}

impl StructuredBlock {
    /// Iterate over bytecode offsets contained in this structured block, in order.
    pub fn iter_offsets<'a>(&'a self) -> Box<dyn Iterator<Item = CodeOffset> + 'a> {
        match self {
            StructuredBlock::Basic { lower, upper } => Box::new((*lower)..=(*upper)),
            StructuredBlock::Seq(blocks) => {
                Box::new(blocks.iter().flat_map(|block| block.iter_offsets()))
            }
            StructuredBlock::IfThenElse {
                then_branch,
                else_branch,
                ..
            } => {
                let then_iter = then_branch.iter_offsets();
                if let Some(else_block) = else_branch {
                    let else_iter = else_block.iter_offsets();
                    Box::new(then_iter.chain(else_iter))
                } else {
                    then_iter
                }
            }
            StructuredBlock::IfElseChain {
                branches,
                else_branch,
            } => {
                let chain_iter = branches.iter().flat_map(|(_, body)| body.iter_offsets());
                if let Some(else_block) = else_branch {
                    let else_iter = else_block.iter_offsets();
                    Box::new(chain_iter.chain(else_iter))
                } else {
                    Box::new(chain_iter)
                }
            }
        }
    }

    /// Convert nested IfThenElse structures into an IfElseChain if they form a chain pattern.
    pub fn optimize_to_chain(self) -> Self {
        match self {
            StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch,
            } => Self::build_chain_from_if(cond_at, then_branch, else_branch),
            other => other,
        }
    }

    /// Convert an IfElseChain into nested IfThenElse structures.
    /// `if c1 { A } else if c2 { B } else { C }` becomes `if c1 { A } else { if c2 { B } else { C } }`
    pub fn chain_to_if_then_else(self) -> Self {
        match self {
            StructuredBlock::IfElseChain {
                branches,
                else_branch,
            } => {
                let mut result = else_branch;

                for (cond_at, then_branch) in branches.into_iter().rev() {
                    result = Some(Box::new(StructuredBlock::IfThenElse {
                        cond_at,
                        then_branch,
                        else_branch: result,
                    }));
                }

                *result.unwrap()
            }
            other => other,
        }
    }

    /// Build the chain from the inside of the IfThenElse by looping over every else that's found
    fn build_chain_from_if(
        first_cond: CodeOffset,
        first_then: Box<StructuredBlock>,
        mut current_else: Option<Box<StructuredBlock>>,
    ) -> Self {
        let mut branches: Vec<(CodeOffset, Box<StructuredBlock>)> = vec![(first_cond, first_then)];

        while let Some(else_block) = current_else {
            match *else_block {
                StructuredBlock::IfThenElse {
                    cond_at,
                    then_branch,
                    else_branch,
                } => {
                    branches.push((cond_at, then_branch));
                    current_else = else_branch;
                }
                StructuredBlock::Seq(blocks) => match Self::unwrap_seq_for_chain(blocks) {
                    SeqUnwrapResult::Advanced {
                        next_cond,
                        next_then,
                        next_else,
                    } => {
                        branches.push((next_cond, next_then));
                        current_else = next_else;
                    }
                    SeqUnwrapResult::NotChain(restored) => {
                        current_else = Some(Box::new(StructuredBlock::Seq(restored)));
                        break;
                    }
                },
                other => {
                    current_else = Some(Box::new(other));
                    break;
                }
            }
        }

        if branches.len() > 1 {
            StructuredBlock::IfElseChain {
                branches,
                else_branch: current_else,
            }
        } else {
            let (cond_at, then_branch) = branches.into_iter().next().unwrap();
            StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch: current_else,
            }
        }
    }

    /// Tries to unwrap a sequential block into a IfElseChain
    fn unwrap_seq_for_chain(mut blocks: Vec<StructuredBlock>) -> SeqUnwrapResult {
        // Pattern 1: Single IfThenElse inside the Seq
        if blocks.len() == 1 {
            let single = blocks.pop().unwrap();
            if let StructuredBlock::IfThenElse {
                cond_at,
                then_branch,
                else_branch,
            } = single
            {
                return SeqUnwrapResult::Advanced {
                    next_cond: cond_at,
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

        if let StructuredBlock::IfThenElse {
            cond_at,
            then_branch,
            mut else_branch,
        } = if_block
        {
            if !remaining.is_empty() {
                if let Some(else_content) = else_branch.take() {
                    remaining.insert(0, *else_content);
                }
                else_branch = Some(Box::new(StructuredBlock::Seq(remaining)));
            }

            return SeqUnwrapResult::Advanced {
                next_cond: cond_at,
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
        next_cond: CodeOffset,
        next_then: Box<StructuredBlock>,
        next_else: Option<Box<StructuredBlock>>,
    },
    /// No chain
    NotChain(Vec<StructuredBlock>),
}
