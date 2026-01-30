// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Cleanup pass for TheoremIR
//!
//! Transformations:
//! 1. Remove identity assignments: `let x := x` -> removed
//! 2. Simplify boolean if expressions: `if cond then true else false` -> `cond`
//! 3. Convert nested boolean ifs to AND: `if A then B else false` -> `A && B`

use crate::data::variables::TypeContext;
use crate::{BinOp, Const, IRNode, Type};

pub fn cleanup(node: IRNode, ctx: &TypeContext) -> IRNode {
    let node = flatten_blocks(node);
    let node = remove_identity_lets(node);
    let node = simplify_boolean_ifs(node);
    let node = convert_boolean_ifs_to_and_or(node, ctx);

    collapse_branch_bindings(node)
}

/// Flatten single-child blocks and merge nested blocks
fn flatten_blocks(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::Block { children } if children.len() == 1 => {
            // Single-child block: unwrap
            children.into_iter().next().unwrap()
        }
        IRNode::Block { mut children } => {
            // Flatten nested blocks at the end
            if let Some(IRNode::Block { children: inner }) = children.last().cloned() {
                children.pop();
                children.extend(inner);
            }
            IRNode::Block { children }
        }
        other => other,
    })
}

/// Remove identity let bindings: `let x := x` -> removed
pub fn remove_identity_lets(node: IRNode) -> IRNode {
    node.filter(|n| !is_identity_let(n))
}

fn is_identity_let(ir: &IRNode) -> bool {
    single_pattern_let(ir)
        .map(|(name, value)| matches!(value, IRNode::Var(v) if v == name))
        .unwrap_or(false)
}

fn single_pattern_let(ir: &IRNode) -> Option<(&String, &IRNode)> {
    match ir {
        IRNode::Let { pattern, value } if pattern.len() == 1 => Some((&pattern[0], value.as_ref())),
        _ => None,
    }
}

/// Get the effective value if it's a boolean constant (possibly wrapped in Block/Return)
fn get_bool_const(node: &IRNode) -> Option<bool> {
    match node {
        IRNode::Const(Const::Bool(b)) => Some(*b),
        IRNode::Block { children } if children.len() == 1 => get_bool_const(&children[0]),
        IRNode::Return(values) if values.len() == 1 => get_bool_const(&values[0]),
        _ => None,
    }
}

/// Simplify boolean if expressions recursively
/// - `if cond then true else false` -> `cond`
/// - `if cond then false else true` -> `!cond`
fn simplify_boolean_ifs(node: IRNode) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Check if both branches are boolean constants (handles wrapped cases)
            let then_is_true = get_bool_const(&then_branch) == Some(true);
            let then_is_false = get_bool_const(&then_branch) == Some(false);
            let else_is_true = get_bool_const(&else_branch) == Some(true);
            let else_is_false = get_bool_const(&else_branch) == Some(false);

            if then_is_true && else_is_false {
                // if cond then true else false -> cond
                *cond
            } else if then_is_false && else_is_true {
                // if cond then false else true -> !cond
                IRNode::UnOp {
                    op: crate::UnOp::Not,
                    operand: cond,
                }
            } else {
                // Keep as is
                IRNode::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
        }
        other => other,
    })
}

/// Convert nested boolean if patterns to AND/OR operations
/// Patterns:
/// - `if cond1 then cond2 else false` -> `cond1 && cond2` (short-circuit AND)
/// - `if cond1 then true else cond2` -> `cond1 || cond2` (short-circuit OR)
fn convert_boolean_ifs_to_and_or(node: IRNode, ctx: &TypeContext) -> IRNode {
    node.map(&mut |n| match n {
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            // Check for both branches being the same boolean constant
            // if X then true else true => true, if X then false else false => false
            if let (Some(then_val), Some(else_val)) =
                (get_bool_const(&then_branch), get_bool_const(&else_branch))
            {
                if then_val == else_val {
                    // Both branches same constant - return that constant
                    return IRNode::Const(Const::Bool(then_val));
                }
            }

            let then_is_true = get_bool_const(&then_branch) == Some(true);
            let then_is_false = get_bool_const(&then_branch) == Some(false);
            let else_is_true = get_bool_const(&else_branch) == Some(true);
            let else_is_false = get_bool_const(&else_branch) == Some(false);

            // Pattern: if cond1 then cond2 else false -> cond1 && cond2 (short-circuit AND)
            if else_is_false && !then_is_false {
                // Check if then_branch is a boolean expression using type tracking
                if is_boolean_type(&then_branch, ctx) {
                    // Convert to AND operation: cond1 && cond2
                    return IRNode::BinOp {
                        op: BinOp::And,
                        lhs: cond,
                        rhs: then_branch,
                    };
                }
            }

            // Pattern: if cond1 then true else cond2 -> cond1 || cond2 (short-circuit OR)
            if then_is_true && !else_is_true {
                // Check if else_branch is a boolean expression using type tracking
                if is_boolean_type(&else_branch, ctx) {
                    // Convert to OR operation: cond1 || cond2
                    return IRNode::BinOp {
                        op: BinOp::Or,
                        lhs: cond,
                        rhs: else_branch,
                    };
                }
            }

            // Keep as is
            IRNode::If {
                cond,
                then_branch,
                else_branch,
            }
        }
        other => other,
    })
}

/// Check if an IR node has a boolean type using the full TypeContext
fn is_boolean_type(node: &IRNode, ctx: &TypeContext) -> bool {
    node.get_type(ctx)
        .map(|ty| matches!(ty, Type::Bool))
        .unwrap_or(false)
}

/// Collapse common patterns where a variable is bound and immediately used.
///
/// Pattern 1 (Block followed by Var):
/// ```
/// Block {
///     If { then: Block { Let { x = v1 } }, else: Block { Let { x = v2 } } },
///     Var("x")
/// }
/// ```
/// Transformed to: `If { then: v1, else: v2 }`
///
/// Pattern 2 (Let followed by Var in same block):
/// ```
/// Block { Let { x = v }, Var("x") }
/// ```
/// Transformed to: `v`
///
/// These patterns arise from Move code that assigns to a variable in branches
/// but our temp inlining can't track that the variable is defined in all branches.
fn collapse_branch_bindings(node: IRNode) -> IRNode {
    // Run to fixpoint since transformations can expose new patterns
    let mut result = node;
    loop {
        let prev = result.clone();
        result = collapse_once(result);
        if result == prev {
            break;
        }
    }
    result
}

fn collapse_once(node: IRNode) -> IRNode {
    node.map(&mut |n| {
        if let IRNode::Block { children } = n {
            if children.len() >= 2 {
                let last_idx = children.len() - 1;
                let prev_idx = children.len() - 2;

                // Pattern 1: [..., Let { x = v }, Var("x")] -> [..., v]
                if let (Some(IRNode::Let { pattern, value }), Some(IRNode::Var(var_name))) =
                    (children.get(prev_idx), children.get(last_idx))
                {
                    if pattern.len() == 1 && &pattern[0] == var_name {
                        let val = (**value).clone();
                        if children.len() == 2 {
                            return val;
                        } else {
                            let mut new_children: Vec<_> = children[..prev_idx].to_vec();
                            new_children.push(val);
                            return IRNode::Block {
                                children: new_children,
                            };
                        }
                    }
                }

                // Pattern 2: [..., If { ... }, Var("x")] where branches bind x
                if let (
                    Some(IRNode::Var(var_name)),
                    Some(IRNode::If {
                        cond,
                        then_branch,
                        else_branch,
                    }),
                ) = (children.get(last_idx), children.get(prev_idx))
                {
                    if let (Some(then_val), Some(else_val)) = (
                        extract_single_let_value(then_branch, var_name),
                        extract_single_let_value(else_branch, var_name),
                    ) {
                        let new_if = IRNode::If {
                            cond: cond.clone(),
                            then_branch: Box::new(then_val),
                            else_branch: Box::new(else_val),
                        };

                        if children.len() == 2 {
                            return new_if;
                        } else {
                            let mut new_children: Vec<_> = children[..prev_idx].to_vec();
                            new_children.push(new_if);
                            return IRNode::Block {
                                children: new_children,
                            };
                        }
                    }
                }
            }
            IRNode::Block { children }
        } else {
            n
        }
    })
}

/// Extract the value from a Block containing a single Let binding to the given variable name.
/// Returns the value if the block is: Block { [Let { pattern: [name], value }] }
fn extract_single_let_value(node: &IRNode, var_name: &str) -> Option<IRNode> {
    match node {
        IRNode::Block { children } if children.len() == 1 => {
            if let IRNode::Let { pattern, value } = &children[0] {
                if pattern.len() == 1 && pattern[0] == var_name {
                    return Some((**value).clone());
                }
            }
            None
        }
        IRNode::Let { pattern, value } => {
            if pattern.len() == 1 && pattern[0] == var_name {
                return Some((**value).clone());
            }
            None
        }
        _ => None,
    }
}
