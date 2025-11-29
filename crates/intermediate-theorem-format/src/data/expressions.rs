// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use crate::data::structure::TheoremStructID;
use crate::data::statements::Statement;
use crate::data::types::TheoremType;
use crate::TheoremFunctionID;
use ethnum::U256;
use num::BigUint;
use serde::{Deserialize, Serialize};

/// Traverse child expressions of an expression.
/// Takes a ref pattern (`(ref)` or `(ref mut)`), an expression action, a vec action, and a block action.
macro_rules! traverse_expr {
    ($target:expr, (ref $($mut:ident)?), $expr_action:expr, $vec_action:expr, $block_action:expr) => {
        match $target {
            Expression::BinOp { ref $($mut)? lhs, ref $($mut)? rhs, .. } => {
                $expr_action(lhs);
                $expr_action(rhs);
            }
            Expression::UnOp { operand: ref $($mut)? operand, .. } => $expr_action(operand),
            Expression::Cast { value: ref $($mut)? value, .. } => $expr_action(value),
            Expression::FieldAccess { operand: ref $($mut)? operand, .. } => $expr_action(operand),
            Expression::Unpack { operand: ref $($mut)? operand, .. } => $expr_action(operand),
            Expression::Call { args: ref $($mut)? args, .. } => $vec_action(args),
            Expression::Pack { fields: ref $($mut)? fields, .. } => $vec_action(fields),
            Expression::VecOp { operands: ref $($mut)? operands, .. } => $vec_action(operands),
            Expression::Tuple(ref $($mut)? exprs) => $vec_action(exprs),
            Expression::IfExpr { condition: ref $($mut)? condition, then_block: ref $($mut)? then_block, else_block: ref $($mut)? else_block } => {
                $expr_action(condition);
                $block_action(then_block);
                $block_action(else_block);
            }
            Expression::WhileExpr { condition: ref $($mut)? condition, body: ref $($mut)? body } => {
                $block_action(condition);
                $block_action(body);
            }
            Expression::Var(_) | Expression::Constant(_) => {}
        }
    };
}

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

/// Expression in the IR.
/// Uses named variables with shadowing semantics (like Lean's `let`).
#[derive(Debug, Clone)]
pub enum Expression {
    /// Variable reference by name.
    /// Uses shadowing semantics: inner definitions shadow outer ones.
    Var(String),

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
        /// Type arguments for generic structs (e.g., Coin<SUI> has type_args = [SUI])
        type_args: Vec<TheoremType>,
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

    /// While loop expression - executes body while condition is true.
    /// Loop state variables are derived implicitly from assignments in the body.
    /// Initial values are the current values of those variables in the outer scope.
    WhileExpr {
        /// Block that computes the loop condition (result should be bool)
        condition: Block,
        /// Block that computes the next state
        body: Block,
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
    pub statements: Vec<Statement>,
    /// The result expression (what the block evaluates to)
    pub result: Box<Expression>,
}

impl Block {
    /// Create a new block with statements and a result
    pub fn new(statements: Vec<Statement>, result: Expression) -> Self {
        Self { statements, result: Box::new(result) }
    }

    /// Create a block that just returns a value (no statements)
    pub fn pure(result: Expression) -> Self {
        Self { statements: Vec::new(), result: Box::new(result) }
    }

    /// Check if this block contains monadic operations
    pub fn is_monadic(&self) -> bool {
        self.statements.iter().any(|s| s.is_monadic())
            || self.result.is_monadic()
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

    /// Substitute variable names in all expressions in this block.
    pub fn substitute_vars(self, subst_map: &std::collections::BTreeMap<String, String>) -> Block {
        Block {
            statements: self.statements.into_iter()
                .map(|s| s.map_expressions(|e| e.substitute_vars(subst_map)))
                .collect(),
            result: Box::new(self.result.substitute_vars(subst_map)),
        }
    }

    /// Mutably traverse all expressions in this block
    pub fn traverse_expressions_mut<F: Fn(&mut Expression)>(&mut self, f: &F) {
        for stmt in &mut self.statements {
            stmt.traverse_expressions_mut(f);
        }
        self.result.traverse_mut(f);
    }

    /// Iterate over all expressions in this block (statements + result)
    pub fn iter_expressions(&self) -> impl Iterator<Item = &Expression> {
        self.statements.iter()
            .flat_map(|s| s.iter_expressions())
            .chain(std::iter::once(&*self.result))
    }
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

    /// Check if this expression produces a monadic result (requires ← binding).
    /// Recursively checks nested blocks for monadic operations.
    /// For IfExpr, also checks if the condition contains monadic calls, since that
    /// requires wrapping the whole if in a `do` block, making it monadic.
    pub fn is_monadic(&self) -> bool {
        match self {
            Expression::Call { convention: CallConvention::Monadic, .. } => true,
            Expression::WhileExpr { .. } => true,
            Expression::IfExpr { condition, then_block, else_block } => {
                // If condition contains monadic calls, the if needs `do` wrapper and becomes monadic
                condition.contains_monadic()
                    || then_block.is_monadic() || else_block.is_monadic()
                    || then_block.result.contains_monadic() || else_block.result.contains_monadic()
            }
            _ => false,
        }
    }

    /// Check if this expression contains any monadic subexpressions.
    /// This recursively checks all children, not just the top level.
    /// Used to determine if a let binding needs `←` when inlined monadic calls are present.
    pub fn contains_monadic(&self) -> bool {
        if self.is_monadic() {
            return true;
        }
        match self {
            Expression::BinOp { lhs, rhs, .. } => {
                lhs.contains_monadic() || rhs.contains_monadic()
            }
            Expression::UnOp { operand, .. } | Expression::Cast { value: operand, .. } |
            Expression::FieldAccess { operand, .. } | Expression::Unpack { operand, .. } => {
                operand.contains_monadic()
            }
            Expression::Call { args, .. } => args.iter().any(|a| a.contains_monadic()),
            Expression::Pack { fields, .. } => fields.iter().any(|f| f.contains_monadic()),
            Expression::VecOp { operands, .. } => operands.iter().any(|o| o.contains_monadic()),
            Expression::Tuple(exprs) => exprs.iter().any(|e| e.contains_monadic()),
            Expression::IfExpr { condition, then_block, else_block } => {
                condition.contains_monadic()
                    || then_block.result.contains_monadic()
                    || else_block.result.contains_monadic()
            }
            Expression::WhileExpr { condition, body } => {
                condition.result.contains_monadic()
                    || body.result.contains_monadic()
            }
            Expression::Var(_) | Expression::Constant(_) => false,
        }
    }

    /// Iterate over this expression and all sub-expressions (depth-first).
    /// Includes expressions inside blocks (IfExpr, WhileExpr).
    pub fn iter(&self) -> ExpressionIter<'_> {
        ExpressionIter { stack: vec![self], block_stack: Vec::new() }
    }

    /// Collect all struct IDs from types in this expression (recursively)
    pub fn collect_type_struct_ids(&self) -> Vec<TheoremStructID> {
        self.iter().flat_map(|expr| {
            match expr {
                Expression::Cast { target_type, .. } => target_type.collect_struct_ids(),
                Expression::Call { type_args, .. } |
                Expression::Pack { type_args, .. } => {
                    type_args.iter().flat_map(|ty| ty.collect_struct_ids()).collect()
                }
                _ => Vec::new(),
            }
        }).collect()
    }

    /// Collect all function calls in this expression (recursively)
    pub fn collect_calls(&self) -> Vec<TheoremFunctionID> {
        self.iter().filter_map(|expr| expr.called_function()).collect()
    }

    /// Map over this expression tree, transforming each sub-expression recursively.
    /// Applies f to children first (post-order), then to self.
    pub fn map<F: Fn(Expression) -> Expression + Copy>(self, f: F) -> Expression {
        let transformed = match self {
            Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
                op,
                lhs: Box::new((*lhs).map(f)),
                rhs: Box::new((*rhs).map(f)),
            },
            Expression::UnOp { op, operand } => Expression::UnOp {
                op,
                operand: Box::new((*operand).map(f)),
            },
            Expression::Cast { value, target_type } => Expression::Cast {
                value: Box::new((*value).map(f)),
                target_type,
            },
            Expression::FieldAccess { struct_id, field_index, operand } => Expression::FieldAccess {
                struct_id,
                field_index,
                operand: Box::new((*operand).map(f)),
            },
            Expression::Unpack { struct_id, operand } => Expression::Unpack {
                struct_id,
                operand: Box::new((*operand).map(f)),
            },
            Expression::Call { function, args, type_args, convention } => Expression::Call {
                function,
                args: args.into_iter().map(|e| e.map(f)).collect(),
                type_args,
                convention,
            },
            Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
                struct_id,
                type_args,
                fields: fields.into_iter().map(|e| e.map(f)).collect(),
            },
            Expression::VecOp { op, operands } => Expression::VecOp {
                op,
                operands: operands.into_iter().map(|e| e.map(f)).collect(),
            },
            Expression::Tuple(exprs) => Expression::Tuple(
                exprs.into_iter().map(|e| e.map(f)).collect(),
            ),
            Expression::IfExpr { condition, then_block, else_block } => Expression::IfExpr {
                condition: Box::new((*condition).map(f)),
                then_block: then_block.map_expressions(f),
                else_block: else_block.map_expressions(f),
            },
            Expression::WhileExpr { condition, body } => Expression::WhileExpr {
                condition: condition.map_expressions(f),
                body: body.map_expressions(f),
            },
            expr @ (Expression::Var(_) | Expression::Constant(_)) => expr,
        };
        f(transformed)
    }

    /// Mutably traverse this expression tree.
    /// Applies f to children first (post-order), then to self.
    pub fn traverse_mut<F: Fn(&mut Expression)>(&mut self, f: &F) {
        traverse_expr!(
            self,
            (ref mut),
            |e: &mut Box<Expression>| e.as_mut().traverse_mut(f),
            |v: &mut Vec<Expression>| { for e in v { e.traverse_mut(f); } },
            |b: &mut Block| b.traverse_expressions_mut(f)
        );
        f(self);
    }

    /// Substitute variable names according to a mapping.
    /// With named variables and shadowing, this is rarely needed -
    /// typically only for renaming variables.
    pub fn substitute_vars(self, subst_map: &std::collections::BTreeMap<String, String>) -> Expression {
        self.map(|expr| {
            match expr {
                Expression::Var(name) => {
                    Expression::Var(subst_map.get(&name).cloned().unwrap_or(name))
                }
                other => other,
            }
        })
    }

    /// Iterate over all variable names referenced in this expression (recursive).
    pub fn iter_vars(&self) -> impl Iterator<Item = &str> + '_ {
        self.iter().filter_map(|expr| {
            match expr {
                Expression::Var(name) => Some(name.as_str()),
                _ => None,
            }
        })
    }

    /// Collect all variable names referenced in this expression.
    pub fn collect_vars(&self) -> Vec<String> {
        self.iter_vars().map(|s| s.to_string()).collect()
    }
}

/// Iterator over expressions in an expression tree (depth-first).
/// Includes all expressions inside blocks (IfExpr, WhileExpr).
pub struct ExpressionIter<'a> {
    stack: Vec<&'a Expression>,
    /// Blocks to process (we process block statements' expressions too)
    block_stack: Vec<&'a Block>,
}

impl<'a> Iterator for ExpressionIter<'a> {
    type Item = &'a Expression;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // First try to get an expression from the stack
            if let Some(expr) = self.stack.pop() {
                traverse_expr!(
                    expr,
                    (ref),
                    |e: &'a Box<Expression>| self.stack.push(e),
                    |v: &'a Vec<Expression>| { for e in v { self.stack.push(e); } },
                    |b: &'a Block| self.block_stack.push(b)
                );
                return Some(expr);
            }

            // If no expressions, try to get more from a block
            let block = self.block_stack.pop()?;
            // Push the result expression
            self.stack.push(&block.result);
            // Push all expressions from statements in the block
            for stmt in &block.statements {
                for expr in stmt.iter_expressions() {
                    self.stack.push(expr);
                }
            }
        }
    }
}
