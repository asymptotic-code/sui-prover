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
//! 2. **Simple traversal**: `children()`, `map()`, `fold()` work uniformly

use crate::data::structure::StructID;
use crate::data::types::{TempId, Type};
use crate::data::variables::TypeContext;
use crate::FunctionID;
use ethnum::U256;
use num::BigUint;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::{fmt, mem};

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
            IRNode::BitOp(bit_op) => {
                match bit_op {
                    BitOp::Extract { operand, .. } => {
                        let $value = operand.$deref();
                        $action;
                    }
                    BitOp::Concat { high, low } => {
                        let $value = high.$deref();
                        $action;
                        let $value = low.$deref();
                        $action;
                    }
                    BitOp::ZeroExtend { operand, .. } | BitOp::SignExtend { operand, .. } => {
                        let $value = operand.$deref();
                        $action;
                    }
                }
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
            IRNode::While { cond, body, invariants, .. } => {
                let $value = cond.$deref();
                $action;
                let $value = body.$deref();
                $action;
                for $value in invariants {
                    $action;
                }
            }
            IRNode::WhileAborts { cond, body_aborts, body_pure, invariants, .. } => {
                let $value = cond.$deref();
                $action;
                let $value = body_aborts.$deref();
                $action;
                let $value = body_pure.$deref();
                $action;
                for $value in invariants {
                    $action;
                }
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

    /// Bit-level operation (extract, concat, extend)
    BitOp(BitOp),

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
        /// Loop invariants (for verification)
        invariants: Vec<IRNode>,
    },

    /// While loop abort predicate (for .aborts variant)
    /// Captures both the abort condition and the pure body for reasoning
    WhileAborts {
        cond: Box<IRNode>,
        body_aborts: Box<IRNode>,
        body_pure: Box<IRNode>,
        vars: Vec<TempId>,
        invariants: Vec<IRNode>,
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
        IRNode::Block { children: vec![] }
    }
}

/// Constant values
#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    Bool(bool),
    UInt { bits: usize, value: U256 },
    Address(BigUint),
    /// Vector constant with element type and values
    Vector { elem_type: Type, elems: Vec<Const> },
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Const::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Const::UInt { value, .. } => write!(f, "{}", value),
            Const::Address(addr) => write!(f, "{}", addr),
            Const::Vector { elems, .. } => {
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    BitNot,
    /// Cast to unsigned integer with specified bit width (8, 16, 32, 64, 128, 256)
    Cast(u32),
}

/// Bit-level operations (extract, concat, extend)
#[derive(Debug, Clone, PartialEq)]
pub enum BitOp {
    /// Extract bits [high:low] from operand
    Extract {
        high: u32,
        low: u32,
        operand: Box<IRNode>,
    },
    /// Concatenate high and low bitvectors
    Concat {
        high: Box<IRNode>,
        low: Box<IRNode>,
    },
    /// Zero-extend by n bits
    ZeroExtend {
        bits: u32,
        operand: Box<IRNode>,
    },
    /// Sign-extend by n bits
    SignExtend {
        bits: u32,
        operand: Box<IRNode>,
    },
}

impl IRNode {
    /// Create a unit value ()
    pub fn unit() -> IRNode {
        IRNode::Tuple(vec![])
    }

    /// Get references to all nodes (including itself) recursively in this IR tree
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=&'a IRNode> + 'a {
        fn collect_nodes<'a>(node: &'a IRNode, result: &mut Vec<&'a IRNode>) {
            result.push(node);
            traverse_ir!(node, as_ir_ref, |child| collect_nodes(child, result));
        }
        let mut result = Vec::new();
        collect_nodes(self, &mut result);
        result.into_iter()
    }

    /// Get references to direct children (depth 1) of this IR node
    pub fn iter_children<'a>(&'a self) -> impl Iterator<Item=&'a IRNode> + 'a {
        let mut result = Vec::new();
        traverse_ir!(self, as_ir_ref, |child| result.push(child));
        result.into_iter()
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

    /// Fold over all IRNodes into a given structure
    pub fn fold<T, F>(&self, init: T, mut f: F) -> T
    where
        F: FnMut(T, &IRNode) -> T,
    {
        self.iter().fold(init, |acc, node| f(acc, node))
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

    /// Filter out nodes from blocks based on a predicate.
    /// Nodes for which the predicate returns false are removed.
    /// This traverses the entire IR tree and filters Block children.
    pub fn filter<F: Fn(&IRNode) -> bool>(self, predicate: F) -> Self {
        self.transform_block(|children| {
            children.into_iter().filter(&predicate).collect()
        })
    }

    /// Check if this is an atomic expression (doesn't need parens when used as arg)
    pub fn is_atomic(&self) -> bool {
        match self {
            IRNode::Var(_) | IRNode::Const(_) | IRNode::Tuple(_) => true,
            // Block with no statements that has an atomic result is also atomic
            IRNode::Block { children } => {
                if children.len() == 1 {
                    children[0].is_atomic()
                } else {
                    false
                }
            }
            // Return with a single atomic value is atomic
            IRNode::Return(values) => values.len() == 1 && values[0].is_atomic(),
            _ => false,
        }
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

    /// Extract and collect values from matching nodes in the IR tree
    /// The extractor function returns Some(T) for nodes that should be collected.
    pub fn extract<T, F>(&self, extractor: F) -> Vec<T>
    where
        F: Fn(&IRNode) -> Option<T>,
    {
        self.iter().filter_map(extractor).collect()
    }

    /// Collect all variable names used (read) in this IR tree
    pub fn used_vars(&self) -> impl Iterator<Item=&TempId> {
        self.iter().filter_map(|node| match node {
            IRNode::Var(name) => Some(name),
            _ => None,
        })
    }

    /// Collect all variable names defined (bound) in this IR tree
    pub fn defined_vars(&self) -> impl Iterator<Item=&TempId> {
        self.iter().flat_map(|node| match node {
            IRNode::Let { pattern, .. } => pattern.iter(),
            _ => [].iter(),
        })
    }

    /// Check if this IR tree contains any While loops
    pub fn has_while_loop(&self) -> bool {
        self.iter().any(|node| matches!(node, IRNode::While { .. } | IRNode::WhileAborts { .. }))
    }

    /// Check if this IR tree contains an early return/abort inside a while loop.
    /// This pattern cannot be properly translated to functional loop combinators.
    pub fn has_early_return_in_while(&self) -> bool {
        fn check_while_body(body: &IRNode) -> bool {
            body.iter().any(|node| matches!(node, IRNode::Return(_) | IRNode::Abort(_)))
        }

        self.iter().any(|node| match node {
            IRNode::While { body, .. } => check_while_body(body),
            IRNode::WhileAborts { body_pure, body_aborts, .. } => {
                check_while_body(body_pure) || check_while_body(body_aborts)
            }
            _ => false,
        })
    }

    /// Collect all function calls
    pub fn calls(&self) -> impl Iterator<Item=FunctionID> + '_ {
        self.iter().filter_map(|node| match node {
            IRNode::Call { function, .. } => Some(*function),
            _ => None,
        })
    }

    /// Rewrite function calls to use a different variant.
    /// Only rewrites Runtime variant calls where `should_rewrite(base_id)` returns true.
    /// Calls already at a non-Runtime variant (like Aborts) are left unchanged.
    pub fn to_variant<F>(self, variant: crate::FunctionVariant, should_rewrite: F) -> Self
    where
        F: Fn(usize) -> bool,
    {
        self.map(&mut |n| match n {
            IRNode::Call { function, type_args, args } => {
                // Only rewrite Runtime variant calls - preserve other variants like Aborts
                let new_function = if function.is_runtime() && should_rewrite(function.base) {
                    function.to_variant(variant)
                } else {
                    function
                };
                IRNode::Call {
                    function: new_function,
                    type_args,
                    args,
                }
            }
            other => other,
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

    /// Check if this IR tree contains any Abort nodes
    pub fn aborts(&self) -> bool {
        self.iter().any(|n| matches!(n, IRNode::Abort(_)))
    }

    /// Check if ALL execution paths in this IR tree lead to Abort
    pub fn always_aborts(&self) -> bool {
        match self {
            IRNode::Abort(_) => true,
            IRNode::Block { children } => {
                children.last().map_or(false, |c| c.always_aborts())
            }
            IRNode::If { then_branch, else_branch, .. } => {
                then_branch.always_aborts() && else_branch.always_aborts()
            }
            IRNode::While { .. } => false, // Loops might not execute
            IRNode::Return(_) => false, // Returns don't abort
            _ => false,
        }
    }

    /// Get the abort code if this IR is an abort (or ends in one)
    pub fn get_abort_code(&self) -> Option<&IRNode> {
        match self {
            IRNode::Abort(code) => Some(code),
            IRNode::Block { children } => children.last().and_then(|c| c.get_abort_code()),
            _ => None,
        }
    }

    /// Check if the expression is monadic
    pub fn is_monadic(&self) -> bool {
        self.iter().any(|n| match n {
            IRNode::Call { function, .. } if function.is_runtime() => true,
            _ => false
        })
    }

    /// Substitute variables according to a mapping
    pub fn substitute_vars(self, subs: &BTreeMap<String, String>) -> IRNode {
        self.map(&mut |node| match node {
            IRNode::Var(name) => IRNode::Var(subs.get(&name).cloned().unwrap_or(name)),
            IRNode::While { cond, body, vars, invariants } => {
                // Also substitute variable names in the vars metadata
                let vars = vars
                    .into_iter()
                    .map(|v| subs.get(&v).cloned().unwrap_or(v))
                    .collect();
                IRNode::While { cond, body, vars, invariants }
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
    pub fn iter_struct_references(&self) -> impl Iterator<Item=StructID> + '_ {
        self.iter().filter_map(|node| match node {
            IRNode::Pack { struct_id, .. }
            | IRNode::Unpack { struct_id, .. }
            | IRNode::Field { struct_id, .. }
            | IRNode::UpdateField { struct_id, .. } => Some(*struct_id),
            _ => None,
        })
    }

    /// Collect all struct IDs referenced in type positions (type arguments)
    pub fn iter_type_struct_ids(&self) -> impl Iterator<Item=StructID> + '_ {
        self.iter()
            .filter_map(|node| match node {
                IRNode::Pack { type_args, .. } | IRNode::Call { type_args, .. } => {
                    Some(type_args.iter())
                }
                _ => None,
            })
            .flatten()
            .flat_map(|ty| ty.struct_ids())
    }

    pub fn combine(self, other: IRNode) -> IRNode {
        let mut elements: Vec<_> = self.into();
        elements.append(&mut other.into());
        elements.into_iter().collect()
    }

    /// Get the type of this IR expression using the type context.
    /// Returns None for control flow nodes (Return, Abort) and spec nodes (Requires, Ensures).
    /// Panics if a node that should have a type cannot resolve it.
    pub fn get_type(&self, ctx: &TypeContext) -> Option<Type> {
        match self {
            // Variables: look up in registry - MUST exist
            IRNode::Var(name) => Some(ctx.vars.get_type_or_panic(name).clone()),

            // Constants: direct type inference
            IRNode::Const(c) => Some(match c {
                Const::Bool(_) => Type::Bool,
                Const::UInt { bits, .. } => Type::UInt(*bits as u32),
                Const::Address(_) => Type::Address,
                Const::Vector { elem_type, .. } => Type::Vector(Box::new(elem_type.clone())),
            }),

            // Binary operations: result type depends on operation
            IRNode::BinOp { op, lhs, .. } => Some(match op {
                BinOp::And | BinOp::Or |
                BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Type::Bool,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
                | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                    lhs.expect_type(ctx)
                }
            }),

            // Unary operations
            IRNode::UnOp { op, operand } => Some(match op {
                UnOp::Not => Type::Bool,
                UnOp::BitNot => operand.expect_type(ctx),
                UnOp::Cast(bits) => Type::UInt(*bits),
            }),

            // Bit operations
            IRNode::BitOp(bit_op) => Some(match bit_op {
                BitOp::Extract { high, low, .. } => Type::UInt(high - low + 1),
                BitOp::Concat { high, low } => {
                    let high_type = high.expect_type(ctx);
                    let low_type = low.expect_type(ctx);
                    match (high_type, low_type) {
                        (Type::UInt(h), Type::UInt(l)) => Type::UInt(h + l),
                        _ => panic!("BitOp::Concat expects UInt operands"),
                    }
                }
                BitOp::ZeroExtend { bits, operand } | BitOp::SignExtend { bits, operand } => {
                    let op_type = operand.expect_type(ctx);
                    match op_type {
                        Type::UInt(orig_bits) => Type::UInt(orig_bits + bits),
                        _ => panic!("BitOp extend expects UInt operand"),
                    }
                }
            }),

            // Function calls: look up return type from context (using base ID)
            IRNode::Call { function, .. } => Some(ctx.function_return_type(function.base).clone()),

            // Struct construction
            IRNode::Pack { struct_id, type_args, .. } => {
                Some(Type::Struct {
                    struct_id: *struct_id,
                    type_args: type_args.clone(),
                })
            }

            // Field access: look up field type from struct definition
            IRNode::Field { struct_id, field_index, .. } => {
                Some(ctx.struct_field_type(*struct_id, *field_index).clone())
            }

            // Struct destructuring: returns tuple of field types
            IRNode::Unpack { struct_id, .. } => Some(ctx.struct_fields_tuple(*struct_id)),

            // Tuples
            IRNode::Tuple(elems) => {
                Some(Type::Tuple(elems.iter().map(|e| e.expect_type(ctx)).collect()))
            }

            // Let: type is the type of the value being bound (if it has one)
            IRNode::Let { value, .. } => value.get_type(ctx),

            // If: type is from the non-terminating branch
            IRNode::If { then_branch, else_branch, .. } => {
                if !then_branch.terminates() {
                    then_branch.get_type(ctx)
                } else {
                    else_branch.get_type(ctx)
                }
            }

            // While: returns tuple of the loop variables
            IRNode::While { vars, .. } => {
                Some(Type::Tuple(vars.iter().map(|v| ctx.vars.get_type_or_panic(v).clone()).collect()))
            }

            // WhileAborts: returns Bool (whether body aborts)
            IRNode::WhileAborts { .. } => Some(Type::Bool),

            // Block: type of last child (if it has one)
            IRNode::Block { children } => {
                children.last().and_then(|c| c.get_type(ctx))
            }

            // Control flow nodes don't have types
            IRNode::Return(_) | IRNode::Abort(_) => None,

            // Updates return the updated value
            IRNode::UpdateField { base, .. } => base.get_type(ctx),
            IRNode::UpdateVec { base, .. } => base.get_type(ctx),

            // Spec nodes don't produce values
            IRNode::Requires(_) | IRNode::Ensures(_) => None,
        }
    }

    /// Get the type of this IR expression, panicking if it doesn't have one.
    /// Use this when you know the node must have a type.
    pub fn expect_type(&self, ctx: &TypeContext) -> Type {
        self.get_type(ctx).unwrap_or_else(|| {
            panic!("Expected IR node to have a type, but it doesn't: {:?}", self)
        })
    }


    /// Simplify blocks by unwrapping simple let-return patterns
    /// Transforms: Block([Let(x, v), Return(x)]) => Return(v)
    pub fn simplify_blocks(self) -> IRNode {
        self.map(&mut |node| match node {
            IRNode::Block { mut children } => {
                // Check for pattern: [Let { pattern: [x], value }, Return([Var(x)])]
                if children.len() == 2 {
                    if let (
                        IRNode::Let { pattern, value: _ },
                        IRNode::Return(ret_vals)
                    ) = (&children[0], &children[1]) {
                        if pattern.len() == 1 && ret_vals.len() == 1 {
                            if let IRNode::Var(var_name) = &ret_vals[0] {
                                if var_name == &pattern[0] {
                                    // Replace with Return(value)
                                    let value = if let IRNode::Let { value, .. } = children.remove(0) {
                                        *value
                                    } else {
                                        unreachable!()
                                    };
                                    return IRNode::Return(vec![value]);
                                }
                            }
                        }
                    }
                }
                IRNode::Block { children }
            }
            other => other,
        })
    }
}

impl Into<Vec<IRNode>> for IRNode {
    fn into(self) -> Vec<IRNode> {
        match self {
            IRNode::Block { children } => {
                children
            }
            IRNode::Tuple(vals) if vals.is_empty() => {
                vec![]
            }
            _ => vec![self]
        }
    }
}

impl FromIterator<IRNode> for IRNode {
    fn from_iter<T: IntoIterator<Item=IRNode>>(iter: T) -> Self {
        let mut nodes = iter.into_iter().collect::<Vec<IRNode>>();

        match nodes.len() {
            0 => IRNode::default(),
            1 => nodes.pop().unwrap(),
            _ => IRNode::Block { children: nodes }
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
