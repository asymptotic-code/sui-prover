// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Cleanup pass for TheoremIR
//!
//! This pass performs several cleanup transformations:
//! 1. Remove identity assignments: `let x := x` -> removed
//! 2. Remove empty sequences: `Sequence([])` -> removed
//! 3. Remove Requires/Ensures statements (spec-only, not needed in impl)
//! 4. Flatten nested sequences
//! 5. Copy propagation: `let tmp := expr; let x := tmp` -> `let x := expr`

use crate::{Block, Expression, LetPattern, Statement};

/// Run all cleanup passes on a statement tree.
/// Returns the cleaned up statement.
pub fn cleanup(stmt: Statement) -> Statement {
    let mut result = stmt;

    // Run cleanup until fixpoint
    loop {
        let cleaned = cleanup_pass(result.clone());
        if statements_equal(&result, &cleaned) {
            break;
        }
        result = cleaned;
    }

    result
}

/// Single pass of cleanup transformations.
fn cleanup_pass(stmt: Statement) -> Statement {
    match stmt {
        Statement::Sequence(stmts) => {
            // First, recursively clean each statement
            let mut cleaned: Vec<Statement> = stmts.into_iter()
                .map(cleanup_pass)
                .flat_map(flatten_sequence)
                .filter(|s| !is_removable_statement(s))
                .collect();

            // Apply copy propagation: let tmp := expr; let x := tmp -> let x := expr
            apply_copy_propagation(&mut cleaned);

            if cleaned.is_empty() {
                Statement::Sequence(vec![])
            } else if cleaned.len() == 1 {
                cleaned.into_iter().next().unwrap()
            } else {
                Statement::Sequence(cleaned)
            }
        }

        Statement::Let { pattern, value, types } => {
            // Check for identity assignment: let x := x
            if is_identity_assignment(&pattern, &value) {
                return Statement::Sequence(vec![]);
            }

            // Clean nested blocks in the value
            Statement::Let {
                pattern,
                value: cleanup_expression(value),
                types,
            }
        }

        Statement::Return { values } => Statement::Return {
            values: values.into_iter().map(cleanup_expression).collect(),
        },

        Statement::Abort { code } => Statement::Abort {
            code: cleanup_expression(code),
        },

        Statement::UpdateField { target, struct_id, field_index, new_value } => Statement::UpdateField {
            target: cleanup_expression(target),
            struct_id,
            field_index,
            new_value: cleanup_expression(new_value),
        },

        Statement::UpdateVectorElement { target, index, new_value } => Statement::UpdateVectorElement {
            target: cleanup_expression(target),
            index: cleanup_expression(index),
            new_value: cleanup_expression(new_value),
        },

        // Keep Requires/Ensures as-is for now (they render as pure ())
        // We filter them out at the sequence level
        stmt @ (Statement::Requires { .. } | Statement::Ensures { .. }) => stmt,
    }
}

/// Apply copy propagation to a sequence of statements.
/// Two patterns:
/// 1. let tmp := expr; let x := tmp -> let x := expr (remove first stmt)
/// 2. Forward substitution: after `let x := tmp`, replace all later uses of `tmp` with `x`
///
/// With named variables, this is simpler: we just look for patterns where
/// a variable is defined and immediately used in another let binding.
fn apply_copy_propagation(stmts: &mut Vec<Statement>) {
    if stmts.len() < 2 {
        return;
    }

    // First pass: identify copy propagation opportunities
    // Collect (index_to_remove, new_stmt_for_next, old_name, new_name)
    let mut propagations: Vec<(usize, Statement, String, String)> = Vec::new();

    for i in 0..stmts.len().saturating_sub(1) {
        // Check if stmt[i] defines a single var with a non-trivial expression
        if let Statement::Let { pattern: LetPattern::Single(def_name), value: def_value, .. } = &stmts[i] {
            // Skip if the definition is just a variable reference (identity, handled elsewhere)
            if matches!(def_value, Expression::Var(_)) {
                continue;
            }

            // Check if stmt[i+1] is just assigning this var to another variable
            if let Statement::Let { pattern: use_pattern, value: Expression::Var(ref use_var), types } = &stmts[i + 1] {
                if use_var == def_name {
                    // Replace: let tmp := expr; let x := tmp -> let x := expr
                    let new_stmt = Statement::Let {
                        pattern: use_pattern.clone(),
                        value: def_value.clone(),
                        types: types.clone(),
                    };

                    // Record forward substitution: tmp -> x
                    if let LetPattern::Single(new_name) = use_pattern {
                        propagations.push((i, new_stmt, def_name.clone(), new_name.clone()));
                    }
                }
            }
        }
    }

    // Second pass: apply propagations
    let mut forward_subs: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    let mut indices_to_remove: Vec<usize> = Vec::new();

    for (idx, new_stmt, old_name, new_name) in propagations {
        stmts[idx + 1] = new_stmt;
        indices_to_remove.push(idx);
        forward_subs.insert(old_name, new_name);
    }

    // Remove the statements that were propagated (in reverse order to preserve indices)
    for i in indices_to_remove.into_iter().rev() {
        stmts.remove(i);
    }

    // Apply forward substitutions to remaining statements
    if !forward_subs.is_empty() {
        for stmt in stmts.iter_mut() {
            *stmt = substitute_vars_in_stmt(stmt.clone(), &forward_subs);
        }
    }
}

/// Substitute variable references in a statement.
fn substitute_vars_in_stmt(stmt: Statement, subs: &std::collections::BTreeMap<String, String>) -> Statement {
    match stmt {
        Statement::Let { pattern, value, types } => Statement::Let {
            pattern,
            value: value.substitute_vars(subs),
            types,
        },
        Statement::Sequence(stmts) => Statement::Sequence(
            stmts.into_iter().map(|s| substitute_vars_in_stmt(s, subs)).collect()
        ),
        Statement::Return { values } => Statement::Return {
            values: values.into_iter().map(|e| e.substitute_vars(subs)).collect(),
        },
        Statement::Abort { code } => Statement::Abort {
            code: code.substitute_vars(subs),
        },
        Statement::UpdateField { target, struct_id, field_index, new_value } => Statement::UpdateField {
            target: target.substitute_vars(subs),
            struct_id,
            field_index,
            new_value: new_value.substitute_vars(subs),
        },
        Statement::UpdateVectorElement { target, index, new_value } => Statement::UpdateVectorElement {
            target: target.substitute_vars(subs),
            index: index.substitute_vars(subs),
            new_value: new_value.substitute_vars(subs),
        },
        Statement::Requires { condition } => Statement::Requires {
            condition: condition.substitute_vars(subs),
        },
        Statement::Ensures { condition } => Statement::Ensures {
            condition: condition.substitute_vars(subs),
        },
    }
}

/// Check if a statement should be removed.
fn is_removable_statement(stmt: &Statement) -> bool {
    match stmt {
        // Remove empty sequences
        Statement::Sequence(stmts) => stmts.is_empty(),
        // Keep Requires/Ensures - they are specification statements that should be preserved
        Statement::Requires { .. } | Statement::Ensures { .. } => false,
        // Remove identity assignments
        Statement::Let { pattern, value, .. } => is_identity_assignment(pattern, value),
        _ => false,
    }
}

/// Check if this is an identity assignment: let x := x
fn is_identity_assignment(pattern: &LetPattern, value: &Expression) -> bool {
    match pattern {
        LetPattern::Single(name) => {
            matches!(value, Expression::Var(var_name) if var_name == name)
        }
        LetPattern::Tuple(_) => false, // Tuple patterns can't be identity
    }
}

/// Flatten a statement into multiple statements if it's a sequence.
fn flatten_sequence(stmt: Statement) -> Vec<Statement> {
    match stmt {
        Statement::Sequence(stmts) if stmts.is_empty() => vec![],
        Statement::Sequence(stmts) => stmts,
        other => vec![other],
    }
}

/// Cleanup expressions, including nested blocks.
fn cleanup_expression(expr: Expression) -> Expression {
    match expr {
        Expression::IfExpr { condition, then_block, else_block } => Expression::IfExpr {
            condition: Box::new(cleanup_expression(*condition)),
            then_block: cleanup_block(then_block),
            else_block: cleanup_block(else_block),
        },

        Expression::WhileExpr { condition, body } => Expression::WhileExpr {
            condition: cleanup_block(condition),
            body: cleanup_block(body),
        },

        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(cleanup_expression(*lhs)),
            rhs: Box::new(cleanup_expression(*rhs)),
        },

        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(cleanup_expression(*operand)),
        },

        Expression::Cast { value, target_type } => Expression::Cast {
            value: Box::new(cleanup_expression(*value)),
            target_type,
        },

        Expression::FieldAccess { struct_id, field_index, operand } => Expression::FieldAccess {
            struct_id,
            field_index,
            operand: Box::new(cleanup_expression(*operand)),
        },

        Expression::Unpack { struct_id, operand } => Expression::Unpack {
            struct_id,
            operand: Box::new(cleanup_expression(*operand)),
        },

        Expression::Call { function, args, type_args, convention } => Expression::Call {
            function,
            args: args.into_iter().map(cleanup_expression).collect(),
            type_args,
            convention,
        },

        Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(cleanup_expression).collect(),
        },

        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(cleanup_expression).collect(),
        },

        Expression::Tuple(exprs) => Expression::Tuple(
            exprs.into_iter().map(cleanup_expression).collect(),
        ),

        expr @ (Expression::Var(_) | Expression::Constant(_)) => expr,
    }
}

/// Cleanup a block: clean statements and result.
fn cleanup_block(block: Block) -> Block {
    let cleaned_stmts = cleanup_pass(Statement::Sequence(block.statements));
    let statements = match cleaned_stmts {
        Statement::Sequence(stmts) => stmts,
        other => vec![other],
    };

    // Filter out empty sequences and removable statements
    let filtered: Vec<Statement> = statements.into_iter()
        .filter(|s| !is_removable_statement(s))
        .collect();

    Block {
        statements: filtered,
        result: Box::new(cleanup_expression(*block.result)),
    }
}

/// Simple structural equality check for statements (for fixpoint detection).
fn statements_equal(a: &Statement, b: &Statement) -> bool {
    format!("{:?}", a) == format!("{:?}", b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConstantValue, TheoremType};
    use ethnum::U256;

    #[test]
    fn test_removes_identity_assignment() {
        // let x := x
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("x".to_string()),
                value: Expression::Var("x".to_string()),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("y".to_string())],
            },
        ]);

        let cleaned = cleanup(body);

        // Should only have the return statement
        if let Statement::Return { .. } = cleaned {
            // Good - single statement collapsed
        } else if let Statement::Sequence(stmts) = cleaned {
            assert_eq!(stmts.len(), 1);
            assert!(matches!(stmts[0], Statement::Return { .. }));
        } else {
            panic!("Expected Return or Sequence with Return");
        }
    }

    #[test]
    fn test_preserves_requires_ensures() {
        let body = Statement::Sequence(vec![
            Statement::Requires {
                condition: Expression::Constant(ConstantValue::Bool(true)),
            },
            Statement::Let {
                pattern: LetPattern::Single("x".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Ensures {
                condition: Expression::Constant(ConstantValue::Bool(true)),
            },
            Statement::Return {
                values: vec![Expression::Var("x".to_string())],
            },
        ]);

        let cleaned = cleanup(body);

        // Should preserve all 4 statements including requires/ensures
        if let Statement::Sequence(stmts) = cleaned {
            assert_eq!(stmts.len(), 4);
            assert!(matches!(stmts[0], Statement::Requires { .. }));
            assert!(matches!(stmts[1], Statement::Let { .. }));
            assert!(matches!(stmts[2], Statement::Ensures { .. }));
            assert!(matches!(stmts[3], Statement::Return { .. }));
        } else {
            panic!("Expected Sequence");
        }
    }

    #[test]
    fn test_removes_empty_sequence() {
        let body = Statement::Sequence(vec![
            Statement::Sequence(vec![]),
            Statement::Return {
                values: vec![Expression::Var("x".to_string())],
            },
        ]);

        let cleaned = cleanup(body);

        // Should just have the return
        assert!(matches!(cleaned, Statement::Return { .. }));
    }

    #[test]
    fn test_flattens_nested_sequences() {
        let body = Statement::Sequence(vec![
            Statement::Sequence(vec![
                Statement::Let {
                    pattern: LetPattern::Single("a".to_string()),
                    value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(1u32) }),
                    types: vec![TheoremType::UInt(32)],
                },
            ]),
            Statement::Let {
                pattern: LetPattern::Single("b".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(2u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("b".to_string())],
            },
        ]);

        let cleaned = cleanup(body);

        // Should be a flat sequence with 3 statements
        if let Statement::Sequence(stmts) = cleaned {
            assert_eq!(stmts.len(), 3);
        } else {
            panic!("Expected Sequence");
        }
    }

    #[test]
    fn test_copy_propagation() {
        // let tmp := if cond then 1 else 2
        // let x := tmp
        // return x
        let if_expr = Expression::IfExpr {
            condition: Box::new(Expression::Var("cond".to_string())),
            then_block: Block {
                statements: vec![],
                result: Box::new(Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(1u32) })),
            },
            else_block: Block {
                statements: vec![],
                result: Box::new(Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(2u32) })),
            },
        };

        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("tmp".to_string()),
                value: if_expr,
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Let {
                pattern: LetPattern::Single("x".to_string()),
                value: Expression::Var("tmp".to_string()),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Return {
                values: vec![Expression::Var("x".to_string())],
            },
        ]);

        let cleaned = cleanup(body);

        // Should be:
        // let x := if cond then 1 else 2
        // return x
        if let Statement::Sequence(stmts) = cleaned {
            assert_eq!(stmts.len(), 2);
            // First should be Let with IfExpr, pattern = "x"
            if let Statement::Let { pattern: LetPattern::Single(name), value, .. } = &stmts[0] {
                assert_eq!(name, "x");
                assert!(matches!(value, Expression::IfExpr { .. }));
            } else {
                panic!("Expected Let");
            }
        } else {
            panic!("Expected Sequence");
        }
    }
}
