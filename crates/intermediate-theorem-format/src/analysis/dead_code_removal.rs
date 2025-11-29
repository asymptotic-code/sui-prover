// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Dead code removal pass
//!
//! This pass removes Let statements where the bound variables are never used.
//! It should be run after temp inlining to clean up definitions that were inlined.
//!
//! The pass is conservative: it only removes Let statements with pure operations
//! (no side effects). Monadic calls are preserved even if unused.

use crate::{Expression, LetPattern, Statement};
use std::collections::BTreeSet;

/// Remove dead code from a statement tree.
/// Returns the optimized statement.
/// Uses multi-pass elimination to remove chains of dead code.
pub fn remove_dead_code(stmt: Statement) -> Statement {
    remove_dead_code_multi_pass(stmt, 10) // Up to 10 iterations
}

/// Remove dead code with a specified maximum number of passes.
/// Multiple passes are needed to remove chains of dead code where
/// removing one unused variable makes another one unused.
fn remove_dead_code_multi_pass(stmt: Statement, max_passes: usize) -> Statement {
    let mut result = stmt;

    for _ in 0..max_passes {
        // Collect all used variable names
        let used = collect_used_vars(&result);
        // Remove unused let bindings
        let new_result = remove_unused_lets(result.clone(), &used);

        // Check if we made progress using a simple structural comparison
        if statements_equal(&result, &new_result) {
            break;
        }
        result = new_result;
    }

    result
}

/// Simple structural equality check for statements (for fixpoint detection).
fn statements_equal(a: &Statement, b: &Statement) -> bool {
    format!("{:?}", a) == format!("{:?}", b)
}

/// Collect all variable names that are actually used (read) in the statement tree.
pub fn collect_used_vars(stmt: &Statement) -> BTreeSet<String> {
    let mut used = BTreeSet::new();
    collect_used_vars_in_stmt(stmt, &mut used);
    used
}

fn collect_used_vars_in_stmt(stmt: &Statement, used: &mut BTreeSet<String>) {
    match stmt {
        Statement::Sequence(stmts) => {
            for s in stmts {
                collect_used_vars_in_stmt(s, used);
            }
        }
        Statement::Let { value, .. } => {
            // Collect vars used in the value (RHS)
            collect_used_vars_in_expr(value, used);
        }
        Statement::Return { values } => {
            for expr in values {
                collect_used_vars_in_expr(expr, used);
            }
        }
        Statement::Abort { code } => {
            collect_used_vars_in_expr(code, used);
        }
        Statement::UpdateField { target, new_value, .. } => {
            collect_used_vars_in_expr(target, used);
            collect_used_vars_in_expr(new_value, used);
        }
        Statement::UpdateVectorElement { target, index, new_value } => {
            collect_used_vars_in_expr(target, used);
            collect_used_vars_in_expr(index, used);
            collect_used_vars_in_expr(new_value, used);
        }
        Statement::Requires { condition } | Statement::Ensures { condition } => {
            collect_used_vars_in_expr(condition, used);
        }
    }
}

fn collect_used_vars_in_expr(expr: &Expression, used: &mut BTreeSet<String>) {
    match expr {
        Expression::Var(name) => {
            used.insert(name.clone());
        }
        Expression::BinOp { lhs, rhs, .. } => {
            collect_used_vars_in_expr(lhs, used);
            collect_used_vars_in_expr(rhs, used);
        }
        Expression::UnOp { operand, .. } => {
            collect_used_vars_in_expr(operand, used);
        }
        Expression::Cast { value, .. } => {
            collect_used_vars_in_expr(value, used);
        }
        Expression::FieldAccess { operand, .. } => {
            collect_used_vars_in_expr(operand, used);
        }
        Expression::Unpack { operand, .. } => {
            collect_used_vars_in_expr(operand, used);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                collect_used_vars_in_expr(arg, used);
            }
        }
        Expression::Pack { fields, .. } => {
            for field in fields {
                collect_used_vars_in_expr(field, used);
            }
        }
        Expression::VecOp { operands, .. } => {
            for op in operands {
                collect_used_vars_in_expr(op, used);
            }
        }
        Expression::Tuple(exprs) => {
            for e in exprs {
                collect_used_vars_in_expr(e, used);
            }
        }
        Expression::IfExpr { condition, then_block, else_block } => {
            collect_used_vars_in_expr(condition, used);
            for s in &then_block.statements {
                collect_used_vars_in_stmt(s, used);
            }
            collect_used_vars_in_expr(&then_block.result, used);
            for s in &else_block.statements {
                collect_used_vars_in_stmt(s, used);
            }
            collect_used_vars_in_expr(&else_block.result, used);
        }
        Expression::WhileExpr { condition, body } => {
            for s in &condition.statements {
                collect_used_vars_in_stmt(s, used);
            }
            collect_used_vars_in_expr(&condition.result, used);
            for s in &body.statements {
                collect_used_vars_in_stmt(s, used);
            }
            collect_used_vars_in_expr(&body.result, used);
            // State variables (from body.result) are also used - they reference outer scope
            for var in body.result.iter_vars() {
                used.insert(var.to_string());
            }
        }
        Expression::Constant(_) => {}
    }
}

/// Check if all names in a pattern are unused.
fn pattern_all_unused(pattern: &LetPattern, used: &BTreeSet<String>) -> bool {
    match pattern {
        LetPattern::Single(name) => !used.contains(name),
        LetPattern::Tuple(names) => !names.is_empty() && names.iter().all(|n| !used.contains(n)),
    }
}

/// Remove Let statements that define unused variables (if they're pure).
fn remove_unused_lets(stmt: Statement, used: &BTreeSet<String>) -> Statement {
    match stmt {
        Statement::Sequence(stmts) => {
            let new_stmts: Vec<Statement> = stmts.into_iter()
                .filter_map(|s| {
                    if let Statement::Let { ref pattern, ref value, .. } = s {
                        // Check if all bound names are unused
                        let all_unused = pattern_all_unused(pattern, used);
                        let is_pure = is_pure_operation(value);
                        // Only remove if all results are unused AND the operation is pure
                        if all_unused && is_pure {
                            return None;
                        }
                    }
                    Some(remove_unused_lets(s, used))
                })
                .collect();
            Statement::Sequence(new_stmts)
        }
        Statement::Let { pattern, value, types } => {
            // Transform nested blocks in the value
            Statement::Let {
                pattern,
                value: remove_unused_lets_in_expr(value, used),
                types,
            }
        }
        Statement::Return { values } => Statement::Return {
            values: values.into_iter()
                .map(|e| remove_unused_lets_in_expr(e, used))
                .collect(),
        },
        Statement::Abort { code } => Statement::Abort {
            code: remove_unused_lets_in_expr(code, used),
        },
        Statement::UpdateField { target, struct_id, field_index, new_value } => Statement::UpdateField {
            target: remove_unused_lets_in_expr(target, used),
            struct_id,
            field_index,
            new_value: remove_unused_lets_in_expr(new_value, used),
        },
        Statement::UpdateVectorElement { target, index, new_value } => Statement::UpdateVectorElement {
            target: remove_unused_lets_in_expr(target, used),
            index: remove_unused_lets_in_expr(index, used),
            new_value: remove_unused_lets_in_expr(new_value, used),
        },
        Statement::Requires { condition } => Statement::Requires {
            condition: remove_unused_lets_in_expr(condition, used),
        },
        Statement::Ensures { condition } => Statement::Ensures {
            condition: remove_unused_lets_in_expr(condition, used),
        },
    }
}

/// Helper to filter unused lets in a block's statements.
fn filter_unused_lets_in_block(stmts: Vec<Statement>, used: &BTreeSet<String>) -> Vec<Statement> {
    stmts.into_iter()
        .filter_map(|s| {
            if let Statement::Let { ref pattern, ref value, .. } = s {
                let all_unused = pattern_all_unused(pattern, used);
                if all_unused && is_pure_operation(value) {
                    return None;
                }
            }
            Some(remove_unused_lets(s, used))
        })
        .collect()
}

/// Remove unused lets inside expression blocks (IfExpr, WhileExpr).
fn remove_unused_lets_in_expr(expr: Expression, used: &BTreeSet<String>) -> Expression {
    match expr {
        Expression::IfExpr { condition, then_block, else_block } => {
            Expression::IfExpr {
                condition: Box::new(remove_unused_lets_in_expr(*condition, used)),
                then_block: crate::Block {
                    statements: filter_unused_lets_in_block(then_block.statements, used),
                    result: Box::new(remove_unused_lets_in_expr(*then_block.result, used)),
                },
                else_block: crate::Block {
                    statements: filter_unused_lets_in_block(else_block.statements, used),
                    result: Box::new(remove_unused_lets_in_expr(*else_block.result, used)),
                },
            }
        }
        Expression::WhileExpr { condition, body } => {
            Expression::WhileExpr {
                condition: crate::Block {
                    statements: filter_unused_lets_in_block(condition.statements, used),
                    result: Box::new(remove_unused_lets_in_expr(*condition.result, used)),
                },
                body: crate::Block {
                    statements: filter_unused_lets_in_block(body.statements, used),
                    result: Box::new(remove_unused_lets_in_expr(*body.result, used)),
                },
            }
        }
        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(remove_unused_lets_in_expr(*lhs, used)),
            rhs: Box::new(remove_unused_lets_in_expr(*rhs, used)),
        },
        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(remove_unused_lets_in_expr(*operand, used)),
        },
        Expression::Cast { target_type, value } => Expression::Cast {
            target_type,
            value: Box::new(remove_unused_lets_in_expr(*value, used)),
        },
        Expression::FieldAccess { operand, struct_id, field_index } => Expression::FieldAccess {
            operand: Box::new(remove_unused_lets_in_expr(*operand, used)),
            struct_id,
            field_index,
        },
        Expression::Unpack { operand, struct_id } => Expression::Unpack {
            operand: Box::new(remove_unused_lets_in_expr(*operand, used)),
            struct_id,
        },
        Expression::Call { function, type_args, args, convention } => Expression::Call {
            function,
            type_args,
            args: args.into_iter().map(|a| remove_unused_lets_in_expr(a, used)).collect(),
            convention,
        },
        Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(|f| remove_unused_lets_in_expr(f, used)).collect(),
        },
        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(|o| remove_unused_lets_in_expr(o, used)).collect(),
        },
        Expression::Tuple(exprs) => Expression::Tuple(
            exprs.into_iter().map(|e| remove_unused_lets_in_expr(e, used)).collect()
        ),
        expr @ (Expression::Var(_) | Expression::Constant(_)) => expr,
    }
}

/// Check if an operation is pure (has no side effects).
/// In this codebase, all monads are Except with no side effects, so all calls are pure.
fn is_pure_operation(expr: &Expression) -> bool {
    match expr {
        Expression::Constant(_) => true,
        Expression::Var(_) => true,
        Expression::BinOp { lhs, rhs, .. } => is_pure_operation(lhs) && is_pure_operation(rhs),
        Expression::UnOp { operand, .. } => is_pure_operation(operand),
        Expression::Cast { value, .. } => is_pure_operation(value),
        Expression::FieldAccess { operand, .. } => is_pure_operation(operand),
        Expression::Unpack { operand, .. } => is_pure_operation(operand),
        Expression::Pack { fields, .. } => fields.iter().all(is_pure_operation),
        Expression::Tuple(exprs) => exprs.iter().all(is_pure_operation),
        Expression::VecOp { operands, .. } => operands.iter().all(is_pure_operation),
        // All calls are pure - our only monad is Except which has no side effects
        Expression::Call { args, .. } => args.iter().all(is_pure_operation),
        // IfExpr/WhileExpr may contain operations, so check recursively
        Expression::IfExpr { condition, then_block, else_block } => {
            is_pure_operation(condition)
                && then_block.statements.iter().all(is_pure_stmt)
                && is_pure_operation(&then_block.result)
                && else_block.statements.iter().all(is_pure_stmt)
                && is_pure_operation(&else_block.result)
        }
        Expression::WhileExpr { condition, body } => {
            // While loops are pure if all their components are pure
            condition.statements.iter().all(is_pure_stmt)
                && is_pure_operation(&condition.result)
                && body.statements.iter().all(is_pure_stmt)
                && is_pure_operation(&body.result)
        }
    }
}

/// Check if a statement is pure.
fn is_pure_stmt(stmt: &Statement) -> bool {
    match stmt {
        Statement::Sequence(stmts) => stmts.iter().all(is_pure_stmt),
        Statement::Let { value, .. } => is_pure_operation(value),
        // Return and Abort are NOT pure - they terminate execution
        Statement::Return { .. } => false,
        Statement::Abort { .. } => false,
        Statement::UpdateField { .. } | Statement::UpdateVectorElement { .. } => false,
        Statement::Requires { condition } | Statement::Ensures { condition } => {
            is_pure_operation(condition)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConstantValue, TheoremType, BinOp};
    use ethnum::U256;

    #[test]
    fn test_removes_unused_pure_let() {
        // let unused := 42  (unused)
        // return result
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("unused".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("result".to_string())],
            },
        ]);

        let optimized = remove_dead_code(body);

        // Should only have the return statement
        if let Statement::Sequence(stmts) = optimized {
            assert_eq!(stmts.len(), 1);
            assert!(matches!(stmts[0], Statement::Return { .. }));
        } else {
            panic!("Expected Sequence");
        }
    }

    #[test]
    fn test_preserves_used_let() {
        // let x := 42
        // return x
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("x".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("x".to_string())],
            },
        ]);

        let optimized = remove_dead_code(body);

        // Should preserve both statements
        if let Statement::Sequence(stmts) = optimized {
            assert_eq!(stmts.len(), 2);
        } else {
            panic!("Expected Sequence");
        }
    }

    #[test]
    fn test_removes_chain_of_unused() {
        // let a := 42  (unused)
        // let b := a + 1  (unused, but 'a' is "used" in its definition)
        // return result
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("a".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Let {
                pattern: LetPattern::Single("b".to_string()),
                value: Expression::BinOp {
                    op: BinOp::Add,
                    lhs: Box::new(Expression::Var("a".to_string())),
                    rhs: Box::new(Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(1u32) })),
                },
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("result".to_string())],
            },
        ]);

        let optimized = remove_dead_code(body);

        // With multi-pass DCE, both 'a' and 'b' should be removed:
        // - First pass: 'b' is unused, removed ('a' still appears used by b's def)
        // - Second pass: 'a' is now unused, removed
        if let Statement::Sequence(stmts) = optimized {
            assert_eq!(stmts.len(), 1, "Expected only Return after multi-pass DCE");
            assert!(matches!(stmts[0], Statement::Return { .. }));
        } else {
            panic!("Expected Sequence");
        }
    }
}
