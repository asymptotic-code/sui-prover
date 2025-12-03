// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified Intermediate Representation (IR) for TheoremIR
//!
//! This module provides a single recursive type that represents all program constructs.
//! In a functional language like Lean, everything is an expression - a "block" is just
//! nested let bindings, and "statements" are just expressions with effects.
//!
//! ## Design Principles
//!
//! 1. **Single recursive type**: No separate Statement/Expression/Block types
//! 2. **Simple traversal**: `children()`, `transform()`, `fold()` work uniformly
//! 3. **Let-based sequencing**: `Let { value, body }` chains expressions
//! 4. **Everything produces a value**: Even effects like Abort produce unit

use crate::data::structure::StructID;
use crate::data::types::{TempId, Type};
use crate::FunctionID;
use ethnum::U256;
use num::BigUint;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::{fmt, mem};
// ============================================================================
// Traversal Macro
// ============================================================================

/// Traverse child IR nodes of an IR expression.
/// Uses tt for actions to expand inline, avoiding closure lifetime issues.
/// Pass `as_ir_ref` for immutable access, `as_ir_mut` for mutable access.
macro_rules! traverse_ir {
    ($target:expr, $deref:ident, |$value:ident| $action:expr) => {
        match $target {
            IRNode::Var(_) | IRNode::Const(_) => {}
            IRNode::BinOp { lhs, rhs, .. } => {
                let $value = lhs.$deref();
                $action;
                let $value = rhs.$deref();
                $action;
            }
            IRNode::UnOp { operand, .. } => {
                let $value = operand.$deref();
                $action;
            }
            IRNode::Call { args, .. } => {
                for $value in args {
                    $action;
                }
            }
            IRNode::Pack { fields, .. } => {
                for $value in fields {
                    $action;
                }
            }
            IRNode::Field { base, .. } => {
                let $value = base.$deref();
                $action;
            }
            IRNode::Unpack { value, .. } => {
                let $value = value.$deref();
                $action;
            }
            IRNode::VecOp { args, .. } => {
                for $value in args {
                    $action;
                }
            }
            IRNode::Tuple(elems) => {
                for $value in elems {
                    $action;
                }
            }
            IRNode::Block { children } => {
                for $value in children {
                    $action;
                }
            }
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let $value = cond.$deref();
                $action;
                let $value = then_branch.$deref();
                $action;
                let $value = else_branch.$deref();
                $action;
            }
            IRNode::While { cond, body, .. } => {
                let $value = cond.$deref();
                $action;
                let $value = body.$deref();
                $action;
            }
            IRNode::Let { value, .. } => {
                let $value = value.$deref();
                $action;
            }
            IRNode::Return(values) => {
                for $value in values {
                    $action;
                }
            }
            IRNode::Abort(code) => {
                let $value = code.$deref();
                $action;
            }
            IRNode::UpdateField { base, value, .. } => {
                let $value = base.$deref();
                $action;
                let $value = value.$deref();
                $action;
            }
            IRNode::UpdateVec { base, index, value } => {
                let $value = base.$deref();
                $action;
                let $value = index.$deref();
                $action;
                let $value = value.$deref();
                $action;
            }
            IRNode::Requires(cond) => {
                let $value = cond.$deref();
                $action;
            }
            IRNode::Ensures(cond) => {
                let $value = cond.$deref();
                $action;
            }
        }
    };
}

// ============================================================================
// Core IR Type
// ============================================================================

/// The unified IR type. Everything is an expression.
#[derive(Debug, Clone, PartialEq)]
pub enum IRNode {
    // === Atoms ===
    /// Variable reference by name
    Var(TempId),

    /// Constant value
    Const(Const),

    // === Compound Expressions ===
    /// Binary operation: lhs op rhs
    BinOp {
        op: BinOp,
        lhs: Box<IRNode>,
        rhs: Box<IRNode>,
    },

    /// Unary operation: op operand
    UnOp {
        op: UnOp,
        operand: Box<IRNode>,
    },

    /// Function call: function(args)
    Call {
        function: FunctionID,
        type_args: Vec<Type>,
        args: Vec<IRNode>,
    },

    /// Struct construction: StructName { fields... }
    Pack {
        struct_id: StructID,
        type_args: Vec<Type>,
        fields: Vec<IRNode>,
    },

    /// Field access: struct.field
    Field {
        struct_id: StructID,
        field_index: usize,
        base: Box<IRNode>,
    },

    /// Struct destructuring: let (f1, f2, ...) = struct
    Unpack {
        struct_id: StructID,
        value: Box<IRNode>,
    },

    /// Vector operation
    VecOp {
        op: VecOp,
        args: Vec<IRNode>,
    },

    /// Tuple: (a, b, c) or unit ()
    Tuple(Vec<IRNode>),

    /// Let binding: let pattern = value in body
    Let {
        /// Variable names to bind (empty = wildcard, single = simple, multiple = tuple)
        pattern: Vec<TempId>,
        /// The value being bound
        value: Box<IRNode>,
    },

    // === Control Flow (all produce values) ===
    /// Conditional: if cond then t else e
    If {
        cond: Box<IRNode>,
        then_branch: Box<IRNode>,
        else_branch: Box<IRNode>,
    },

    /// While loop: while cond do body
    /// Returns the final state tuple
    While {
        cond: Box<IRNode>,
        body: Box<IRNode>,
        /// Loop state variables that are carried across iterations.
        vars: Vec<TempId>,
    },

    // === Sequencing ===
    Block {
        children: Vec<IRNode>,
    },

    // === Effects ===
    /// Return from function (early return)
    Return(Vec<IRNode>),

    /// Abort execution with error code
    Abort(Box<IRNode>),

    /// Field update: { struct with field = value }
    UpdateField {
        base: Box<IRNode>,
        struct_id: StructID,
        field_index: usize,
        value: Box<IRNode>,
    },

    /// Vector element update: vec.set(index, value)
    UpdateVec {
        base: Box<IRNode>,
        index: Box<IRNode>,
        value: Box<IRNode>,
    },

    // === Specification ===
    /// Precondition assertion (rendered as comment)
    Requires(Box<IRNode>),

    /// Postcondition assertion (rendered as comment)
    Ensures(Box<IRNode>),
}

impl Default for IRNode {
    fn default() -> Self {
        IRNode::Tuple(vec![])
    }
}

/// Constant values
#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    Bool(bool),
    UInt { bits: usize, value: U256 },
    Address(BigUint),
    Vector(Vec<Const>),
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Const::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Const::UInt { value, .. } => write!(f, "{}", value),
            Const::Address(addr) => write!(f, "{}", addr),
            Const::Vector(elems) => {
                write!(f, "[")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", e)?;
                }
                write!(f, "]")
            }
        }
    }
}

/// Binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    // Logical
    And,
    Or,
    // Comparison
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
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
pub enum VecOp {
    Empty,
    Length,
    Push,
    Pop,
    Borrow,
    BorrowMut,
    Swap,
}

impl IRNode {
    /// Create a unit value ()
    pub fn unit() -> IRNode {
        IRNode::Tuple(vec![])
    }

    /// Get references to all nodes (including itself) in this IR tree
    pub fn children(&self) -> Vec<&IRNode> {
        let mut result = vec![self];
        traverse_ir!(self, as_ir_ref, |child| result.push(child));
        result
    }

    /// Get references to all nodes (including itself) in this IR tree
    pub fn all_nodes(&self) -> Vec<&IRNode> {
        let mut result = vec![self];
        traverse_ir!(self, as_ir_ref, |child| result.extend(child.all_nodes()));
        result
    }

    /// Iterates over all nodes of this IR node
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a IRNode> + 'a {
        self.all_nodes().into_iter()
    }

    /// Iterates over all children of this IR node
    pub fn iter_children<'a>(&'a self) -> impl Iterator<Item = &'a IRNode> + 'a {
        self.children().into_iter()
    }

    /// Transform this IR recursively (bottom-up: children first, then parent)
    pub fn map<F: FnMut(IRNode) -> IRNode>(mut self, f: &mut F) -> IRNode {
        // First recurse into children
        traverse_ir!(&mut self, as_ir_mut, |value| {
            let child = mem::take(value);
            *value = child.map(f);
        });
        // Then apply f to self
        f(self)
    }

    /// Collects all the IRNodes into a given structure
    pub fn collect<F: FnMut(&mut T, &IRNode), T: Default>(&self, mut f: F) -> T {
        self.iter().fold(T::default(), |mut acc, node| {
            f(&mut acc, node);
            acc
        })
    }

    /// Checks if something is true on both branches of ifs instead of either
    pub fn check_branches<F: Fn(&IRNode) -> bool>(&self, f: F) -> bool {
        self.iter_children().any(|node| match node {
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => f(then_branch.as_ref()) && f(else_branch.as_ref()),
            _ => f(node),
        })
    }

    /// Transform all Block nodes recursively
    pub fn transform_block<F: Fn(Vec<IRNode>) -> Vec<IRNode>>(self, f: F) -> Self {
        self.map(&mut |node| match node {
            IRNode::Block { children } => IRNode::Block {
                children: f(children),
            },
            other => other,
        })
    }

    /// Check if this is an atomic expression (doesn't need parens when used as arg)
    pub fn is_atomic(&self) -> bool {
        matches!(self, IRNode::Var(_) | IRNode::Const(_) | IRNode::Tuple(_))
    }

    /// Check if this is a terminating node (Return or Abort at the tail)
    pub fn terminates(&self) -> bool {
        match self {
            IRNode::Return(_) | IRNode::Abort(_) => true,
            IRNode::Block { children } => children.last().is_some_and(|c| c.terminates()),
            IRNode::Let { value, .. } => value.terminates(),
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => then_branch.terminates() && else_branch.terminates(),
            _ => false,
        }
    }

    /// Collect all variable names used (read) in this IR tree
    pub fn used_vars(&self) -> impl Iterator<Item = &TempId> {
        self.iter().filter_map(|node| {
            if let IRNode::Var(name) = node {
                return Some(name);
            }
            None
        })
    }

    /// Collect all variable names defined (bound) in this IR tree
    pub fn defined_vars(&self) -> impl Iterator<Item = &TempId> {
        self.iter()
            .flat_map(|node| {
                if let IRNode::Let { pattern, .. } = node {
                    return Some(pattern.iter());
                }
                None
            })
            .flatten()
    }

    /// Collect all function calls
    pub fn calls(&self) -> impl Iterator<Item =FunctionID> + '_ {
        self.iter().filter_map(|node| {
            if let IRNode::Call { function, .. } = node {
                Some(*function)
            } else {
                None
            }
        })
    }

    /// Check if this IR is a unit value ()
    pub fn is_unit(&self) -> bool {
        matches!(self, IRNode::Tuple(elems) if elems.is_empty())
    }

    /// Get the result expression from a Block IR (last child, or self if not a block)
    pub fn get_block_result(&self) -> &IRNode {
        match self {
            IRNode::Block { children } => children.last().unwrap_or(self),
            _ => self,
        }
    }

    /// Get statements from a Block IR (all but last child)
    pub fn get_block_stmts(&self) -> &[IRNode] {
        match self {
            IRNode::Block { children } if !children.is_empty() => &children[..children.len() - 1],
            _ => &[],
        }
    }

    pub fn aborts(&self) -> bool {
        self.iter().any(|n| matches!(n, IRNode::Abort(_)))
    }

    /// Get the abort code if this IR is an abort (or ends in one)
    pub fn get_abort_code(&self) -> Option<&IRNode> {
        match self {
            IRNode::Abort(code) => Some(code),
            IRNode::Block { children } => children.last().and_then(|c| c.get_abort_code()),
            _ => None,
        }
    }

    /// Check if the TOP-LEVEL expression is monadic (directly returns Except)
    /// This does NOT check children - only whether this expression itself requires ←
    /// The `is_func_monadic` closure looks up whether a function ID returns Except.
    pub fn is_monadic(&self, is_func_monadic: &impl Fn(FunctionID) -> bool) -> bool {
        match self {
            IRNode::Abort(_) => true,
            IRNode::While { body, .. } => body.contains_monadic(is_func_monadic),
            IRNode::Call { function, .. } => is_func_monadic(*function),
            IRNode::If {
                then_branch,
                else_branch,
                ..
            } => then_branch.is_monadic(is_func_monadic) || else_branch.is_monadic(is_func_monadic),
            IRNode::Block { children } => children
                .last()
                .is_some_and(|c| c.is_monadic(is_func_monadic)),
            IRNode::Let { value, .. } => value.is_monadic(is_func_monadic),
            IRNode::Tuple(elems) => {
                // A tuple is monadic if any of its elements are monadic
                // (it will be rendered as a do block)
                elems.iter().any(|e| e.is_monadic(is_func_monadic))
            }
            _ => false,
        }
    }

    /// Check if this expression or any child contains monadic operations
    /// Used to determine if a block needs a `do` wrapper
    /// The `is_func_monadic` closure looks up whether a function ID returns Except.
    pub fn contains_monadic(&self, is_func_monadic: &impl Fn(FunctionID) -> bool) -> bool {
        self.iter().any(|node| match node {
            IRNode::Abort(_) => true,
            IRNode::Call { function, .. } => is_func_monadic(*function),
            _ => false,
        })
    }

    /// Substitute variables according to a mapping
    pub fn substitute_vars(self, subs: &BTreeMap<String, String>) -> IRNode {
        self.map(&mut |node| match node {
            IRNode::Var(name) => IRNode::Var(subs.get(&name).cloned().unwrap_or(name)),
            IRNode::While { cond, body, vars } => {
                // Also substitute variable names in the vars metadata
                let vars = vars
                    .into_iter()
                    .map(|v| subs.get(&v).cloned().unwrap_or(v))
                    .collect();
                IRNode::While { cond, body, vars }
            }
            IRNode::Let { pattern, value } => {
                // Also substitute variable names in let patterns
                let pattern = pattern
                    .into_iter()
                    .map(|v| subs.get(&v).cloned().unwrap_or(v))
                    .collect();
                IRNode::Let { pattern, value }
            }
            other => other,
        })
    }

    /// Extract top-level variable names from a tuple/var expression
    pub fn extract_top_level_vars(&self) -> Vec<&String> {
        match self {
            IRNode::Var(name) => vec![name],
            IRNode::Tuple(elems) => elems
                .iter()
                .flat_map(|e| e.extract_top_level_vars())
                .collect(),
            _ => vec![],
        }
    }

    /// Collect all struct IDs referenced in Pack, Unpack, Field, UpdateField operations
    pub fn iter_struct_references(&self) -> impl Iterator<Item =StructID> + '_ {
        self.iter().filter_map(|node| match node {
            IRNode::Pack { struct_id, .. }
            | IRNode::Unpack { struct_id, .. }
            | IRNode::Field { struct_id, .. }
            | IRNode::UpdateField { struct_id, .. } => Some(*struct_id),
            _ => None,
        })
    }

    /// Collect all struct IDs referenced in type positions (type arguments)
    pub fn iter_type_struct_ids(&self) -> impl Iterator<Item =StructID> + '_ {
        self.iter().flat_map(|node| match node {
            IRNode::Pack { type_args, .. } | IRNode::Call { type_args, .. } => type_args
                .iter()
                .flat_map(|ty| ty.struct_ids())
                .collect::<Vec<_>>(),
            _ => vec![],
        })
    }

    pub fn destructure_let(&self) -> Option<(&Vec<String>, &Box<IRNode>)> {
        match self {
            IRNode::Let { pattern, value } => Some((pattern, value)),
            _ => None,
        }
    }
}

/// This helps with the conversion for the macro
trait AsIRRef<'a> {
    fn as_ir_ref(&'a self) -> &'a IRNode;
}

impl<'a> AsIRRef<'a> for Box<IRNode> {
    fn as_ir_ref(&'a self) -> &'a IRNode {
        self.as_ref()
    }
}

impl<'a> AsIRRef<'a> for IRNode {
    fn as_ir_ref(&'a self) -> &'a IRNode {
        self
    }
}

trait AsIRMut<'a> {
    fn as_ir_mut(&'a mut self) -> &'a mut IRNode;
}

impl<'a> AsIRMut<'a> for Box<IRNode> {
    fn as_ir_mut(&'a mut self) -> &'a mut IRNode {
        self.as_mut()
    }
}

impl<'a> AsIRMut<'a> for IRNode {
    fn as_ir_mut(&'a mut self) -> &'a mut IRNode {
        self
    }
}
