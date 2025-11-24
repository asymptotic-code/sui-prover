// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Loop Variable Substitution
//!
//! Transforms loop bodies to use loop phi variables instead of original temps.
//! In functional loops, the loop state parameters shadow the outer scope variables.
//!
//! Example transformation:
//! ```
//! let x = 0;
//! let y = 1;
//! while (x < 10) {
//!   x = x + 1;  // References outer x, should reference loop parameter
//!   y = y * 2;  // References outer y, should reference loop parameter
//! }
//! ```
//!
//! After substitution:
//! ```
//! let (x', y') = whileLoop
//!   (fun (x, y) => x < 10)     // Condition uses loop parameters
//!   (fun (x, y) =>             // Body uses loop parameters
//!     let x = x + 1
//!     let y = y * 2
//!     pure (x, y)
//!   )
//!   (0, 1)                     // Initial values
//! ```

use intermediate_theorem_format::{Expression, LoopCondition, LoopVariable, Statement, TempId};
use std::collections::BTreeMap;

/// Apply variable substitution to all while loops in a statement tree
pub fn substitute_loop_variables(statement: Statement) -> Statement {
    statement.map(|stmt| match stmt {
        Statement::While { condition, body, loop_vars } => {
            substitute_while_loop(condition, *body, loop_vars)
        }
        statement => statement
    })
}

/// Substitute variables in a while loop
///
/// Creates a mapping from original temps to loop phi_results,
/// then applies this substitution to:
/// 1. The loop condition (so it references the current loop state)
/// 2. The loop body (so all variable references use loop parameters)
fn substitute_while_loop(
    condition: LoopCondition,
    body: Statement,
    loop_vars: Vec<LoopVariable>,
) -> Statement {
    if loop_vars.is_empty() {
        // No loop variables - no substitution needed
        return Statement::While {
            condition,
            body: Box::new(body),
            loop_vars,
        };
    }

    // Build substitution map: original temp ID -> loop phi_result ID
    let mut subst_map: BTreeMap<TempId, TempId> = BTreeMap::new();
    for loop_var in &loop_vars {
        subst_map.insert(loop_var.initial_value, loop_var.phi_result);
        subst_map.insert(loop_var.updated_value, loop_var.phi_result);
    }

    // Substitute in condition recomputation statements and body
    let substituted_condition = LoopCondition {
        recompute: Box::new(condition.recompute.map_expressions(|expr| substitute_expression(expr, &subst_map))),
        condition_var: condition.condition_var,
    };
    let substituted_body =
        body.map_expressions(|expr| substitute_expression(expr, &subst_map));

    Statement::While {
        condition: substituted_condition,
        body: Box::new(substituted_body),
        loop_vars,
    }
}

/// Substitute variables in an expression
fn substitute_expression(expr: Expression, subst_map: &BTreeMap<TempId, TempId>) -> Expression {
    match expr {
        Expression::Temporary(temp_id) => {
            Expression::Temporary(*subst_map.get(&temp_id).unwrap_or(&temp_id))
        }
        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(substitute_expression(*lhs, subst_map)),
            rhs: Box::new(substitute_expression(*rhs, subst_map)),
        },
        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(substitute_expression(*operand, subst_map)),
        },
        Expression::Cast { value, target_type } => Expression::Cast {
            value: Box::new(substitute_expression(*value, subst_map)),
            target_type,
        },
        Expression::Call { function, args, type_args, convention } => Expression::Call {
            function,
            args: args.into_iter().map(|e| substitute_expression(e, subst_map)).collect(),
            type_args,
            convention,
        },
        Expression::Pack { struct_id, fields } => Expression::Pack {
            struct_id,
            fields: fields.into_iter().map(|e| substitute_expression(e, subst_map)).collect(),
        },
        Expression::Unpack { struct_id, field_index, operand } => Expression::Unpack {
            struct_id,
            field_index,
            operand: Box::new(substitute_expression(*operand, subst_map)),
        },
        Expression::UnpackAll { struct_id, operand } => Expression::UnpackAll {
            struct_id,
            operand: Box::new(substitute_expression(*operand, subst_map)),
        },
        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(|e| substitute_expression(e, subst_map)).collect(),
        },
        expr @ Expression::Constant(_) => expr,
    }
}
