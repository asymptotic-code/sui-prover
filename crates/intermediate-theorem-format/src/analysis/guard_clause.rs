// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Guard clause extraction pass for TheoremIR
//!
//! Transforms nested if-else with abort in one branch into guard clauses:
//!
//! Before:
//! ```
//! let result ← if cond then
//!   do
//!     ... main body ...
//!     pure value
//! else
//!   Except.error code
//! ```
//!
//! After:
//! ```
//! if !cond then Except.error code
//! ... main body (un-nested) ...
//! pure value
//! ```
//!
//! This improves readability by reducing nesting for assert-like patterns.

use crate::{Block, Expression, LetPattern, Statement, TheoremType, UnOp};

/// Extract guard clauses from a statement tree.
/// Returns the transformed statement.
pub fn extract_guard_clauses(stmt: Statement) -> Statement {
    // Run until fixpoint
    let mut result = stmt;
    loop {
        let transformed = extract_pass(result.clone());
        if statements_equal(&result, &transformed) {
            break;
        }
        result = transformed;
    }
    result
}

/// Single pass of guard clause extraction.
fn extract_pass(stmt: Statement) -> Statement {
    match stmt {
        Statement::Sequence(stmts) => {
            // First recursively process each statement
            let processed: Vec<Statement> = stmts.into_iter()
                .map(extract_pass)
                .collect();

            // Then try to extract guard clauses from the sequence
            let extracted = extract_guards_from_sequence(processed);

            if extracted.is_empty() {
                Statement::Sequence(vec![])
            } else if extracted.len() == 1 {
                extracted.into_iter().next().unwrap()
            } else {
                Statement::Sequence(extracted)
            }
        }

        stmt @ Statement::Let { .. } => {
            // Try to extract guard from this Let statement directly
            if let Some(extracted) = try_extract_guard(&stmt) {
                // Successfully extracted - return as sequence (or single stmt)
                let processed: Vec<Statement> = extracted.into_iter()
                    .map(extract_pass)
                    .collect();
                if processed.len() == 1 {
                    processed.into_iter().next().unwrap()
                } else {
                    Statement::Sequence(processed)
                }
            } else {
                // No guard to extract - just recurse into expression
                let Statement::Let { pattern, value, types } = stmt else { unreachable!() };
                Statement::Let {
                    pattern,
                    value: extract_from_expression(value),
                    types,
                }
            }
        }

        stmt @ Statement::Return { .. } => {
            // Try to extract guard from this Return statement directly
            if let Some(extracted) = try_extract_guard(&stmt) {
                // Successfully extracted - return as sequence (or single stmt)
                let processed: Vec<Statement> = extracted.into_iter()
                    .map(extract_pass)
                    .collect();
                if processed.len() == 1 {
                    processed.into_iter().next().unwrap()
                } else {
                    Statement::Sequence(processed)
                }
            } else {
                // No guard to extract - just recurse into expression
                let Statement::Return { values } = stmt else { unreachable!() };
                Statement::Return {
                    values: values.into_iter().map(extract_from_expression).collect(),
                }
            }
        }

        Statement::Abort { code } => Statement::Abort {
            code: extract_from_expression(code),
        },

        Statement::UpdateField { target, struct_id, field_index, new_value } => Statement::UpdateField {
            target: extract_from_expression(target),
            struct_id,
            field_index,
            new_value: extract_from_expression(new_value),
        },

        Statement::UpdateVectorElement { target, index, new_value } => Statement::UpdateVectorElement {
            target: extract_from_expression(target),
            index: extract_from_expression(index),
            new_value: extract_from_expression(new_value),
        },

        stmt @ (Statement::Requires { .. } | Statement::Ensures { .. }) => stmt,
    }
}

/// Extract guard clauses from a sequence of statements.
/// Looks for patterns like:
///   let x ← if cond then { ... body ...; pure value } else { Abort code }
/// And transforms to:
///   if !cond then Abort code
///   ... body ...
///   let x := value
fn extract_guards_from_sequence(stmts: Vec<Statement>) -> Vec<Statement> {
    let mut result = Vec::new();

    for stmt in stmts {
        // Check if this is a Let with an IfExpr that has abort in one branch
        if let Some(extracted) = try_extract_guard(&stmt) {
            result.extend(extracted);
        } else {
            result.push(stmt);
        }
    }

    result
}

/// Try to extract a guard clause from a Let or Return statement.
/// Returns Some(extracted_statements) if successful, None otherwise.
fn try_extract_guard(stmt: &Statement) -> Option<Vec<Statement>> {
    // Handle Let with IfExpr
    if let Statement::Let { pattern, value, types } = stmt {
        if let Expression::IfExpr { condition, then_block, else_block } = value {
            return try_extract_guard_from_if(
                condition,
                then_block,
                else_block,
                |then_result| {
                    if !pattern.is_empty() {
                        Some(Statement::Let {
                            pattern: pattern.clone(),
                            value: then_result,
                            types: types.clone(),
                        })
                    } else {
                        None
                    }
                },
            );
        }
    }

    // Handle Return with a single IfExpr value
    if let Statement::Return { values } = stmt {
        if values.len() == 1 {
            if let Expression::IfExpr { condition, then_block, else_block } = &values[0] {
                return try_extract_guard_from_if(
                    condition,
                    then_block,
                    else_block,
                    |then_result| Some(Statement::Return { values: vec![then_result] }),
                );
            }
        }
    }

    None
}

/// Try to extract guard from an if-expression with abort in one branch.
/// `make_final_stmt` creates the final statement from the non-abort branch's result.
fn try_extract_guard_from_if<F>(
    condition: &Box<Expression>,
    then_block: &Block,
    else_block: &Block,
    make_final_stmt: F,
) -> Option<Vec<Statement>>
where
    F: FnOnce(Expression) -> Option<Statement>,
{
    // Pattern 1: else branch is abort (then branch is main body)
    // if cond then { body; value } else { setup; abort }
    // => if !cond then { setup; abort }; body; final_stmt(value)
    // But skip if then_block is trivial (already a guard clause shape)
    if block_is_abort(else_block) && !block_is_trivial(then_block) {
        let abort_stmts = extract_abort_statements(else_block);
        let guard = create_guard_if(negate_condition(condition.as_ref().clone()), abort_stmts);

        let mut extracted = vec![guard];
        extracted.extend(then_block.statements.clone());

        // Add the final statement from the result
        if let Some(final_stmt) = make_final_stmt(*then_block.result.clone()) {
            extracted.push(final_stmt);
        }

        return Some(extracted);
    }

    // Pattern 2: then branch is abort (else branch is main body)
    // if cond then { setup; abort } else { body; value }
    // => if cond then { setup; abort }; body; final_stmt(value)
    // But skip if else_block is trivial (already a guard clause shape)
    if block_is_abort(then_block) && !block_is_trivial(else_block) {
        let abort_stmts = extract_abort_statements(then_block);
        let guard = create_guard_if(condition.as_ref().clone(), abort_stmts);

        let mut extracted = vec![guard];
        extracted.extend(else_block.statements.clone());

        // Add the final statement from the result
        if let Some(final_stmt) = make_final_stmt(*else_block.result.clone()) {
            extracted.push(final_stmt);
        }

        return Some(extracted);
    }

    None
}

/// Check if a block is just an abort (possibly with some setup statements, but result is abort)
fn block_is_abort(block: &Block) -> bool {
    // Check if the block terminates with abort
    // The block "terminates" if its statements contain an Abort
    block.statements.iter().any(|s| matches!(s, Statement::Abort { .. }))
}

/// Check if a block is trivial (empty statements and unit/empty tuple result).
/// This identifies already-extracted guard clauses to prevent infinite recursion.
fn block_is_trivial(block: &Block) -> bool {
    block.statements.is_empty() && matches!(block.result.as_ref(), Expression::Tuple(exprs) if exprs.is_empty())
}

/// Extract all statements from a block that are needed for the abort.
/// This includes setup statements (like constant definitions) and the abort itself.
fn extract_abort_statements(block: &Block) -> Vec<Statement> {
    block.statements.clone()
}

/// Negate a boolean condition
fn negate_condition(cond: Expression) -> Expression {
    // If already negated, unwrap it
    if let Expression::UnOp { op: UnOp::Not, operand } = cond {
        return *operand;
    }

    Expression::UnOp {
        op: UnOp::Not,
        operand: Box::new(cond),
    }
}

/// Create a guard if statement: if cond then { setup; abort } else pure ()
/// The statements parameter should include any setup statements (like constant definitions)
/// followed by the abort statement itself.
fn create_guard_if(condition: Expression, statements: Vec<Statement>) -> Statement {
    Statement::Let {
        pattern: LetPattern::Tuple(vec![]), // Empty tuple pattern for unit
        value: Expression::IfExpr {
            condition: Box::new(condition),
            then_block: Block {
                statements,
                result: Box::new(Expression::Tuple(vec![])),
            },
            else_block: Block {
                statements: vec![],
                result: Box::new(Expression::Tuple(vec![])),
            },
        },
        types: vec![TheoremType::Tuple(vec![])],
    }
}

/// Recursively extract guard clauses from expressions
fn extract_from_expression(expr: Expression) -> Expression {
    match expr {
        Expression::IfExpr { condition, then_block, else_block } => Expression::IfExpr {
            condition: Box::new(extract_from_expression(*condition)),
            then_block: extract_from_block(then_block),
            else_block: extract_from_block(else_block),
        },

        Expression::WhileExpr { condition, body } => Expression::WhileExpr {
            condition: extract_from_block(condition),
            body: extract_from_block(body),
        },

        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(extract_from_expression(*lhs)),
            rhs: Box::new(extract_from_expression(*rhs)),
        },

        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(extract_from_expression(*operand)),
        },

        Expression::Cast { value, target_type } => Expression::Cast {
            value: Box::new(extract_from_expression(*value)),
            target_type,
        },

        Expression::FieldAccess { struct_id, field_index, operand } => Expression::FieldAccess {
            struct_id,
            field_index,
            operand: Box::new(extract_from_expression(*operand)),
        },

        Expression::Unpack { struct_id, operand } => Expression::Unpack {
            struct_id,
            operand: Box::new(extract_from_expression(*operand)),
        },

        Expression::Call { function, args, type_args, convention } => Expression::Call {
            function,
            args: args.into_iter().map(extract_from_expression).collect(),
            type_args,
            convention,
        },

        Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(extract_from_expression).collect(),
        },

        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(extract_from_expression).collect(),
        },

        Expression::Tuple(exprs) => Expression::Tuple(
            exprs.into_iter().map(extract_from_expression).collect(),
        ),

        expr @ (Expression::Var(_) | Expression::Constant(_)) => expr,
    }
}

/// Extract guard clauses from a block
fn extract_from_block(block: Block) -> Block {
    let extracted_stmt = extract_pass(Statement::Sequence(block.statements));
    let statements = match extracted_stmt {
        Statement::Sequence(stmts) => stmts,
        other => vec![other],
    };

    Block {
        statements,
        result: Box::new(extract_from_expression(*block.result)),
    }
}

/// Simple structural equality check for statements (for fixpoint detection)
fn statements_equal(a: &Statement, b: &Statement) -> bool {
    format!("{:?}", a) == format!("{:?}", b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ConstantValue;
    use ethnum::U256;

    #[test]
    fn test_guard_extraction_else_abort() {
        // if cond then { let x := 1; pure x } else { abort 0 }
        // => if !cond then abort 0; let x := 1; let result := x
        let if_expr = Expression::IfExpr {
            condition: Box::new(Expression::Var("cond".to_string())),
            then_block: Block {
                statements: vec![
                    Statement::Let {
                        pattern: LetPattern::Single("x".to_string()),
                        value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                        types: vec![TheoremType::UInt(32)],
                    },
                ],
                result: Box::new(Expression::Var("x".to_string())),
            },
            else_block: Block {
                statements: vec![
                    Statement::Abort {
                        code: Expression::Constant(ConstantValue::UInt { bits: 64, value: U256::ZERO }),
                    },
                ],
                result: Box::new(Expression::Tuple(vec![])),
            },
        };

        let stmt = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("result".to_string()),
                value: if_expr,
                types: vec![TheoremType::UInt(32)],
            },
        ]);

        let extracted = extract_guard_clauses(stmt);

        // Should have: guard if, let x := 42, let result := x
        if let Statement::Sequence(stmts) = extracted {
            assert_eq!(stmts.len(), 3, "Expected 3 statements after extraction");
            // First should be the guard
            assert!(matches!(&stmts[0], Statement::Let { value: Expression::IfExpr { .. }, .. }));
        } else {
            panic!("Expected Sequence");
        }
    }
}
