// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use crate::data::structure::TheoremStructID;
use crate::data::types::{TempId, TheoremType};
use crate::TheoremFunctionID;
use ethnum::U256;
use num::BigUint;
use serde::{Deserialize, Serialize};

/// Constant value that can represent various numeric types
#[derive(Debug, Clone)]
pub enum ConstantValue {
    /// Boolean value
    Bool(bool),
    /// Unsigned integer with specified bit width (8, 16, 32, 64, 128, or 256)
    /// Stored as U256 for uniform representation, with bits indicating the actual type
    UInt { bits: usize, value: U256 },
    /// Address (semantically distinct from generic integers)
    Address(BigUint),
    /// Vector of constants (handles arrays, byte arrays, etc.)
    Vector(Vec<ConstantValue>),
}

impl ConstantValue {
    /// Convert to string representation for Lean output
    pub fn to_string(&self) -> String {
        match self {
            ConstantValue::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            ConstantValue::UInt { value, .. } => value.to_string(),
            ConstantValue::Address(addr) => addr.to_string(),
            ConstantValue::Vector(elements) => format!("[{}]", elements
                        .iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<String>>()
                        .join(", "))
        }
    }
}

/// Specifies how to render the function call
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CallConvention {
    /// Pure call: f(x, y)
    Pure,
    /// Monadic call: do x ← f a b; ...
    Monadic,
}

/// SSA operation
#[derive(Debug, Clone)]
pub enum Expression {
    /// Temporary value
    Temporary(TempId),

    /// Constant value (supports U128, U256, and arbitrary precision)
    Constant(ConstantValue),

    /// Binary operation
    BinOp {
        op: BinOp,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },

    /// Unary operation
    UnOp {
        op: UnOp,
        operand: Box<Expression>,
    },

    /// Cast operation
    Cast {
        value: Box<Expression>,
        target_type: TheoremType,
    },

    /// Function call
    Call {
        function: TheoremFunctionID,
        args: Vec<Expression>,
        type_args: Vec<TheoremType>,
        convention: CallConvention,
    },

    /// Pack (create struct)
    Pack {
        struct_id: TheoremStructID,
        fields: Vec<Expression>,
    },

    /// Access a field
    FieldAccess {
        struct_id: TheoremStructID,
        field_index: usize,
        operand: Box<Expression>,
    },

    /// Unpack all fields (destructure struct - extract all fields as tuple)
    /// Used for multi-result Let statements
    Unpack {
        struct_id: TheoremStructID,
        operand: Box<Expression>,
    },

    /// Vector operation
    VecOp {
        op: VectorOp,
        operands: Vec<Expression>,
    },

    /// Tuple expression (for returning multiple values from blocks)
    Tuple(Vec<Expression>),

    /// If expression - evaluates to a value
    /// Both branches must produce values of the same type
    IfExpr {
        condition: Box<Expression>,
        then_block: Block,
        else_block: Block,
    },

    /// While loop expression - evaluates to final loop state
    /// The loop takes initial state, runs until condition is false,
    /// and returns the final state values
    WhileExpr {
        /// Block that computes the loop condition (result should be bool)
        condition: Block,
        /// Block that computes the next state (result should match state types)
        body: Block,
        /// Loop state: variables, their types, and initial values
        state: LoopState,
    },
}

/// Binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    BitAnd, BitOr, BitXor, Shl, Shr,
    And, Or,
    Eq, Neq, Lt, Le, Gt, Ge,
}

/// Unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnOp {
    Not,
    CastU8,
    CastU16,
    CastU32,
    CastU64,
    CastU128,
    CastU256,
}

/// Vector operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VectorOp {
    Empty,
    Length,
    Push,
    Pop,
    Borrow,
    BorrowMut,
    Swap,
}

/// A block of statements with a final result expression.
/// This is the fundamental unit for if/while branches.
#[derive(Debug, Clone)]
pub struct Block {
    /// Statements to execute
    pub statements: Vec<super::statements::Statement>,
    /// The result expression (what the block evaluates to)
    pub result: Box<Expression>,
}

impl Block {
    /// Create a new block with statements and a result
    pub fn new(statements: Vec<super::statements::Statement>, result: Expression) -> Self {
        Self { statements, result: Box::new(result) }
    }

    /// Create a block that just returns a value (no statements)
    pub fn pure(result: Expression) -> Self {
        Self { statements: Vec::new(), result: Box::new(result) }
    }

    /// Check if this block contains monadic operations
    pub fn is_monadic(&self) -> bool {
        self.statements.iter().any(|s| s.is_monadic())
            || matches!(&*self.result, Expression::Call { convention: CallConvention::Monadic, .. })
    }

    /// Check if this block terminates (ends with Return or Abort in statements)
    pub fn terminates(&self) -> bool {
        self.statements.iter().any(|s| s.terminates())
    }

    /// Map over all expressions in this block
    pub fn map_expressions<F: Fn(Expression) -> Expression + Copy>(self, f: F) -> Block {
        Block {
            statements: self.statements.into_iter()
                .map(|s| s.map_expressions(f))
                .collect(),
            result: Box::new(self.result.map(f)),
        }
    }

    /// Iterate over all expressions in this block (statements + result)
    pub fn iter_expressions(&self) -> impl Iterator<Item = &Expression> {
        self.statements.iter()
            .flat_map(|s| s.iter_expressions())
            .chain(std::iter::once(&*self.result))
    }
}

/// Loop state specification for while loops
#[derive(Debug, Clone)]
pub struct LoopState {
    /// Variables that carry state through the loop (their TempIds)
    pub vars: Vec<TempId>,
    /// Types of the loop state variables
    pub types: Vec<TheoremType>,
    /// Initial values for the state variables
    pub initial: Vec<Expression>,
}

impl Expression {
    /// Extract function ID if this is a Call expression
    pub fn called_function(&self) -> Option<TheoremFunctionID> {
        match self {
            Expression::Call { function, .. } => Some(*function),
            _ => None,
        }
    }

    /// Extract struct ID if this is a Pack or Unpack expression
    pub fn struct_reference(&self) -> Option<TheoremStructID> {
        match self {
            Expression::Pack { struct_id, .. }
            | Expression::FieldAccess { struct_id, .. }
            | Expression::Unpack { struct_id, .. } => Some(*struct_id),
            _ => None,
        }
    }

    /// Collect all struct IDs from types in this expression
    pub fn collect_type_struct_ids(&self) -> Vec<TheoremStructID> {
        let mut result = Vec::new();
        match self {
            Expression::Cast { target_type, .. } => {
                result.extend(target_type.collect_struct_ids());
            }
            Expression::Call { type_args, .. } => {
                for ty in type_args {
                    result.extend(ty.collect_struct_ids());
                }
            }
            _ => {}
        }
        result
    }

    /// Map over this expression tree, transforming each sub-expression recursively.
    /// Applies f to children first (post-order), then to self.
    pub fn map<F: Fn(Expression) -> Expression + Copy>(self, f: F) -> Expression {
        let transformed_children = match self {
            Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
                op,
                lhs: Box::new(lhs.map(f)),
                rhs: Box::new(rhs.map(f)),
            },
            Expression::UnOp { op, operand } => Expression::UnOp {
                op,
                operand: Box::new(operand.map(f)),
            },
            Expression::Cast { value, target_type } => Expression::Cast {
                value: Box::new(value.map(f)),
                target_type,
            },
            Expression::Call { function, args, type_args, convention } => Expression::Call {
                function,
                args: args.into_iter().map(|e| e.map(f)).collect(),
                type_args,
                convention,
            },
            Expression::Pack { struct_id, fields } => Expression::Pack {
                struct_id,
                fields: fields.into_iter().map(|e| e.map(f)).collect(),
            },
            Expression::FieldAccess { struct_id, field_index, operand } => Expression::FieldAccess {
                struct_id,
                field_index,
                operand: Box::new(operand.map(f)),
            },
            Expression::Unpack { struct_id, operand } => Expression::Unpack {
                struct_id,
                operand: Box::new(operand.map(f)),
            },
            Expression::VecOp { op, operands } => Expression::VecOp {
                op,
                operands: operands.into_iter().map(|e| e.map(f)).collect(),
            },
            Expression::Tuple(exprs) => Expression::Tuple(
                exprs.into_iter().map(|e| e.map(f)).collect(),
            ),
            Expression::IfExpr { condition, then_block, else_block } => Expression::IfExpr {
                condition: Box::new(condition.map(f)),
                then_block: then_block.map_expressions(f),
                else_block: else_block.map_expressions(f),
            },
            Expression::WhileExpr { condition, body, state } => Expression::WhileExpr {
                condition: condition.map_expressions(f),
                body: body.map_expressions(f),
                state: LoopState {
                    vars: state.vars,
                    types: state.types,
                    initial: state.initial.into_iter().map(|e| e.map(f)).collect(),
                },
            },
            // Leaf nodes - no children to transform
            expr @ (Expression::Temporary(_) | Expression::Constant(_)) => expr,
        };
        f(transformed_children)
    }

    /// Substitute temporary variables according to a mapping.
    /// This is a common operation used in SSA transformations.
    pub fn substitute_temps(self, subst_map: &std::collections::BTreeMap<TempId, TempId>) -> Expression {
        self.map(|expr| match expr {
            Expression::Temporary(temp_id) => {
                Expression::Temporary(*subst_map.get(&temp_id).unwrap_or(&temp_id))
            }
            other => other,
        })
    }

    /// Iterate over all temporary IDs referenced in this expression (recursive).
    pub fn iter_temps(&self) -> impl Iterator<Item = TempId> + '_ {
        ExprTempIter { stack: vec![self] }
    }

    /// Collect all temporary IDs referenced in this expression.
    pub fn collect_temps(&self) -> Vec<TempId> {
        self.iter_temps().collect()
    }
}

/// Iterator over temporary IDs in an expression tree
struct ExprTempIter<'a> {
    stack: Vec<&'a Expression>,
}

impl<'a> Iterator for ExprTempIter<'a> {
    type Item = TempId;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let expr = self.stack.pop()?;
            match expr {
                Expression::Temporary(temp_id) => return Some(*temp_id),
                Expression::Constant(_) => continue,
                Expression::BinOp { lhs, rhs, .. } => {
                    self.stack.push(rhs);
                    self.stack.push(lhs);
                }
                Expression::UnOp { operand, .. } => self.stack.push(operand),
                Expression::Cast { value, .. } => self.stack.push(value),
                Expression::Call { args, .. } => self.stack.extend(args.iter().rev()),
                Expression::Pack { fields, .. } => self.stack.extend(fields.iter().rev()),
                Expression::FieldAccess { operand, .. } => self.stack.push(operand),
                Expression::Unpack { operand, .. } => self.stack.push(operand),
                Expression::VecOp { operands, .. } => self.stack.extend(operands.iter().rev()),
                Expression::Tuple(exprs) => self.stack.extend(exprs.iter().rev()),
                Expression::IfExpr { condition, then_block, else_block } => {
                    // Push result expressions from blocks
                    self.stack.push(&else_block.result);
                    self.stack.push(&then_block.result);
                    self.stack.push(condition);
                    // Note: statement temps would need a separate iterator
                }
                Expression::WhileExpr { condition, body, state } => {
                    self.stack.push(&body.result);
                    self.stack.push(&condition.result);
                    self.stack.extend(state.initial.iter().rev());
                }
            }
        }
    }
}


