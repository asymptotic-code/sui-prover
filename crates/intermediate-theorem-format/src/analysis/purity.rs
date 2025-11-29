// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Purity analysis pass
//!
//! This pass analyzes functions to determine which are "pure" (cannot abort/throw).
//! Pure functions can have their return types simplified from `Except T` to just `T`,
//! and don't need `do`/`pure` wrapping.
//!
//! A function is pure if:
//! 1. It contains no Abort statements
//! 2. It calls only pure functions (or no functions at all)
//!
//! This requires fixed-point iteration since function purity depends on callee purity.

use crate::{Expression, Statement, TheoremFunction, TheoremFunctionID, TheoremProgram};
use std::collections::BTreeMap;

/// Result of purity analysis for a program.
/// Maps function IDs to whether they are pure (cannot abort).
pub type PurityMap = BTreeMap<TheoremFunctionID, bool>;

/// Analyze purity for all functions in a program.
/// Returns a map from function ID to whether it's pure.
pub fn analyze_purity(program: &TheoremProgram) -> PurityMap {
    // Start with all functions assumed pure (except native functions)
    let mut purity: PurityMap = program.functions.iter()
        .map(|(&id, func)| (id, !func.is_native))
        .collect();

    // Fixed-point iteration: mark functions impure if they abort or call impure functions
    let mut changed = true;
    while changed {
        changed = false;

        for (id, func) in &program.functions {
            if !purity.get(id).copied().unwrap_or(true) {
                // Already marked impure, skip
                continue;
            }

            // Native functions are already marked impure
            if func.is_native {
                continue;
            }

            // Check if this function is actually pure
            if !is_function_pure(func, &purity) {
                purity.insert(*id, false);
                changed = true;
            }
        }
    }

    purity
}

/// Check if a function is pure given current purity knowledge of other functions.
fn is_function_pure(func: &TheoremFunction, purity: &PurityMap) -> bool {
    is_statement_pure(&func.body, purity)
}

/// Check if a statement is pure (no aborts, only pure calls).
fn is_statement_pure(stmt: &Statement, purity: &PurityMap) -> bool {
    match stmt {
        Statement::Sequence(stmts) => stmts.iter().all(|s| is_statement_pure(s, purity)),

        Statement::Let { value, .. } => is_expression_pure(value, purity),

        Statement::Return { values } => values.iter().all(|v| is_expression_pure(v, purity)),

        // Abort makes a function impure
        Statement::Abort { .. } => false,

        Statement::UpdateField { target, new_value, .. } => {
            is_expression_pure(target, purity) && is_expression_pure(new_value, purity)
        }

        Statement::UpdateVectorElement { target, index, new_value } => {
            is_expression_pure(target, purity)
                && is_expression_pure(index, purity)
                && is_expression_pure(new_value, purity)
        }

        // Spec statements don't affect purity (they're comments)
        Statement::Requires { condition } | Statement::Ensures { condition } => {
            is_expression_pure(condition, purity)
        }
    }
}

/// Check if an expression is pure.
fn is_expression_pure(expr: &Expression, purity: &PurityMap) -> bool {
    match expr {
        Expression::Constant(_) | Expression::Var(_) => true,

        Expression::BinOp { lhs, rhs, .. } => {
            is_expression_pure(lhs, purity) && is_expression_pure(rhs, purity)
        }

        Expression::UnOp { operand, .. } => is_expression_pure(operand, purity),

        Expression::Cast { value, .. } => is_expression_pure(value, purity),

        Expression::FieldAccess { operand, .. } => is_expression_pure(operand, purity),

        Expression::Unpack { operand, .. } => is_expression_pure(operand, purity),

        Expression::Call { function, args, .. } => {
            // Check if the called function is pure
            let callee_pure = purity.get(function).copied().unwrap_or(false);
            callee_pure && args.iter().all(|a| is_expression_pure(a, purity))
        }

        Expression::Pack { fields, .. } => {
            fields.iter().all(|f| is_expression_pure(f, purity))
        }

        Expression::VecOp { operands, .. } => {
            operands.iter().all(|o| is_expression_pure(o, purity))
        }

        Expression::Tuple(exprs) => {
            exprs.iter().all(|e| is_expression_pure(e, purity))
        }

        Expression::IfExpr { condition, then_block, else_block } => {
            is_expression_pure(condition, purity)
                && is_block_pure(then_block, purity)
                && is_block_pure(else_block, purity)
        }

        // WhileExpr is always impure because whileLoop is a monadic construct
        // (it can potentially loop forever, making it partial/effectful)
        Expression::WhileExpr { .. } => false,
    }
}

/// Check if a block is pure.
fn is_block_pure(block: &crate::Block, purity: &PurityMap) -> bool {
    block.statements.iter().all(|s| is_statement_pure(s, purity))
        && is_expression_pure(&block.result, purity)
}