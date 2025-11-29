// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Return simplification pass
//!
//! This pass simplifies patterns like:
//!   let x ← call
//!   pure x
//!
//! Into just:
//!   call
//!
//! This makes the generated code cleaner and more idiomatic.

use crate::{Expression, LetPattern, Statement};

/// Simplify return patterns in a statement tree.
pub fn simplify_returns(stmt: Statement) -> Statement {
    simplify_returns_in_stmt(stmt)
}

fn simplify_returns_in_stmt(stmt: Statement) -> Statement {
    match stmt {
        Statement::Sequence(stmts) => {
            // First, recursively simplify all statements
            let mut new_stmts: Vec<Statement> = stmts.into_iter()
                .map(simplify_returns_in_stmt)
                .collect();

            // Now look for pattern: Let followed by Return of just that var
            simplify_let_return_pattern(&mut new_stmts);

            Statement::Sequence(new_stmts)
        }
        Statement::Let { pattern, value, types } => {
            Statement::Let {
                pattern,
                value: simplify_returns_in_expr(value),
                types,
            }
        }
        Statement::Return { values } => Statement::Return {
            values: values.into_iter()
                .map(simplify_returns_in_expr)
                .collect(),
        },
        Statement::Abort { code } => Statement::Abort {
            code: simplify_returns_in_expr(code),
        },
        Statement::UpdateField { target, struct_id, field_index, new_value } => Statement::UpdateField {
            target: simplify_returns_in_expr(target),
            struct_id,
            field_index,
            new_value: simplify_returns_in_expr(new_value),
        },
        Statement::UpdateVectorElement { target, index, new_value } => Statement::UpdateVectorElement {
            target: simplify_returns_in_expr(target),
            index: simplify_returns_in_expr(index),
            new_value: simplify_returns_in_expr(new_value),
        },
        Statement::Requires { condition } => Statement::Requires {
            condition: simplify_returns_in_expr(condition),
        },
        Statement::Ensures { condition } => Statement::Ensures {
            condition: simplify_returns_in_expr(condition),
        },
    }
}

/// Look for pattern: Let { pattern: Single(name), value } followed by Return { values: [Var(name)] }
/// and simplify to just Return { values: [value] }
fn simplify_let_return_pattern(stmts: &mut Vec<Statement>) {
    if stmts.len() < 2 {
        return;
    }

    // Check the last two statements
    let len = stmts.len();
    let last_idx = len - 1;
    let second_last_idx = len - 2;

    // Check if pattern matches
    let should_simplify = match (&stmts[second_last_idx], &stmts[last_idx]) {
        (
            Statement::Let { pattern: LetPattern::Single(def_name), .. },
            Statement::Return { values }
        ) => {
            // Single result, single return value, return is just the defined variable
            values.len() == 1
                && matches!(&values[0], Expression::Var(name) if name == def_name)
        }
        _ => false,
    };

    if should_simplify {
        // Extract the value from the Let
        let value = match stmts.remove(second_last_idx) {
            Statement::Let { value, .. } => value,
            _ => unreachable!(),
        };

        // Replace the Return with one that returns the value directly
        stmts[second_last_idx] = Statement::Return {
            values: vec![value],
        };
    }
}

fn simplify_returns_in_expr(expr: Expression) -> Expression {
    match expr {
        Expression::IfExpr { condition, then_block, else_block } => {
            Expression::IfExpr {
                condition: Box::new(simplify_returns_in_expr(*condition)),
                then_block: simplify_returns_in_block(then_block),
                else_block: simplify_returns_in_block(else_block),
            }
        }
        Expression::WhileExpr { condition, body } => {
            Expression::WhileExpr {
                condition: simplify_returns_in_block(condition),
                body: simplify_returns_in_block(body),
            }
        }
        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(simplify_returns_in_expr(*lhs)),
            rhs: Box::new(simplify_returns_in_expr(*rhs)),
        },
        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(simplify_returns_in_expr(*operand)),
        },
        Expression::Cast { value, target_type } => Expression::Cast {
            value: Box::new(simplify_returns_in_expr(*value)),
            target_type,
        },
        Expression::FieldAccess { struct_id, field_index, operand } => Expression::FieldAccess {
            struct_id,
            field_index,
            operand: Box::new(simplify_returns_in_expr(*operand)),
        },
        Expression::Unpack { struct_id, operand } => Expression::Unpack {
            struct_id,
            operand: Box::new(simplify_returns_in_expr(*operand)),
        },
        Expression::Call { function, args, type_args, convention } => Expression::Call {
            function,
            args: args.into_iter().map(simplify_returns_in_expr).collect(),
            type_args,
            convention,
        },
        Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(simplify_returns_in_expr).collect(),
        },
        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(simplify_returns_in_expr).collect(),
        },
        Expression::Tuple(exprs) => Expression::Tuple(
            exprs.into_iter().map(simplify_returns_in_expr).collect(),
        ),
        expr @ (Expression::Var(_) | Expression::Constant(_)) => expr,
    }
}

fn simplify_returns_in_block(block: crate::Block) -> crate::Block {
    // Convert statements to a sequence, simplify, then extract
    let simplified = simplify_returns_in_stmt(Statement::Sequence(block.statements));
    let mut statements = match simplified {
        Statement::Sequence(s) => s,
        other => vec![other],
    };

    let result = simplify_returns_in_expr(*block.result);

    // Check for pattern: last statement is Let { pattern: Single(name), value },
    // and result is Var(name) - can simplify to just value as result
    if let Some(Statement::Let { pattern: LetPattern::Single(def_name), .. }) = statements.last() {
        if let Expression::Var(ref use_name) = result {
            if use_name == def_name {
                // Pattern matches! Extract value and use as result
                let new_result = match statements.pop() {
                    Some(Statement::Let { value, .. }) => value,
                    _ => unreachable!(),
                };
                return crate::Block {
                    statements,
                    result: Box::new(new_result),
                };
            }
        }
    }

    crate::Block {
        statements,
        result: Box::new(result),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{TheoremType, CallConvention};

    #[test]
    fn test_simplifies_let_return_pattern() {
        // let x ← call()
        // return x
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("x".to_string()),
                value: Expression::Call {
                    function: 42,
                    args: vec![],
                    type_args: vec![],
                    convention: CallConvention::Monadic,
                },
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("x".to_string())],
            },
        ]);

        let simplified = simplify_returns(body);

        // Should be just: return call()
        if let Statement::Sequence(stmts) = simplified {
            assert_eq!(stmts.len(), 1);
            if let Statement::Return { values } = &stmts[0] {
                assert_eq!(values.len(), 1);
                assert!(matches!(&values[0], Expression::Call { .. }));
            } else {
                panic!("Expected Return");
            }
        } else {
            panic!("Expected Sequence");
        }
    }

    #[test]
    fn test_preserves_multi_use_let() {
        // let a ← call()
        // let b := a + a
        // return b
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("a".to_string()),
                value: Expression::Call {
                    function: 42,
                    args: vec![],
                    type_args: vec![],
                    convention: CallConvention::Monadic,
                },
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Let {
                pattern: LetPattern::Single("b".to_string()),
                value: Expression::BinOp {
                    op: crate::BinOp::Add,
                    lhs: Box::new(Expression::Var("a".to_string())),
                    rhs: Box::new(Expression::Var("a".to_string())),
                },
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("b".to_string())],
            },
        ]);

        let simplified = simplify_returns(body);

        // Should simplify the last let+return, but keep the first let
        if let Statement::Sequence(stmts) = simplified {
            assert_eq!(stmts.len(), 2);
            assert!(matches!(&stmts[0], Statement::Let { .. }));
            assert!(matches!(&stmts[1], Statement::Return { .. }));
        } else {
            panic!("Expected Sequence");
        }
    }
}
