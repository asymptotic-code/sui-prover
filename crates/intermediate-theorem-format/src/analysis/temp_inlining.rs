// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Variable inlining analysis pass
//!
//! This pass identifies variables that are only used once and can be safely
//! inlined at their use sites. The goal is to produce cleaner code that matches
//! the original Move source more closely.
//!
//! Example transformation:
//!   let t7 := (1 : UInt32)
//!   let t8 := (abs_tick &&& t7)
//!   let t9 := (0 : UInt32)
//!   let t10 := (t8 != t9)
//!
//! Into:
//!   let t10 := ((abs_tick &&& (1 : UInt32)) != (0 : UInt32))
//!
//! Monadic call inlining (rendered with `(← ...)` syntax):
//!   let t1 ← foo x
//!   let t2 ← bar t1
//!
//! Into:
//!   let t2 ← bar (← foo x)
//!
//! Rules:
//! - Only inline single-use variables within the SAME SCOPE
//! - Monadic calls are inlined with `(← ...)` wrapper in Lean output
//! - Don't inline if/while expressions (they need special rendering)
//! - Don't inline expressions that would result in unreasonable nesting
//!
//! Scope-aware inlining:
//! - Each block (function body, IfExpr branch, WhileExpr condition/body) is its own scope
//! - Variables defined in a scope are analyzed for use WITHIN that scope only
//! - This prevents issues where the same temp name appears in multiple scopes

use crate::{Block, ConstantValue, Expression, LetPattern, Statement, VariableRegistry};
use std::collections::BTreeMap;

/// Result of variable usage analysis
pub struct TempUsageInfo {
    /// How many times each variable name is used (as an Expression::Var)
    pub use_counts: BTreeMap<String, usize>,
    /// Definition site for each variable (the expression assigned to it)
    pub definitions: BTreeMap<String, Expression>,
    /// Whether each variable's definition is monadic (needs `←` in Lean when inlined)
    pub is_monadic: BTreeMap<String, bool>,
}

impl TempUsageInfo {
    /// Analyze a function body to find variable usage counts and definitions
    /// NOTE: This is deprecated - use scope-aware inline_temps_scoped instead
    pub fn analyze(body: &Statement, _registry: &VariableRegistry) -> Self {
        let mut use_counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut definitions: BTreeMap<String, Expression> = BTreeMap::new();
        let mut is_monadic: BTreeMap<String, bool> = BTreeMap::new();

        // First pass: collect definitions and count uses at TOP LEVEL ONLY
        // (not recursing into IfExpr/WhileExpr blocks - those are separate scopes)
        collect_definitions_and_uses_toplevel(body, &mut definitions, &mut use_counts, &mut is_monadic);

        Self { use_counts, definitions, is_monadic }
    }

    /// Check if a variable's definition is monadic (needs `←` when inlined)
    pub fn is_monadic(&self, name: &str) -> bool {
        self.is_monadic.get(name).copied().unwrap_or(false)
    }

    /// Check if a variable should be inlined
    pub fn should_inline(&self, name: &str) -> bool {
        // Must have a definition
        let def = match self.definitions.get(name) {
            Some(d) => d,
            None => return false,
        };

        // Always inline cheap constants (booleans) regardless of use count
        // This enables short-circuit simplification (if c1 then c2 else false => c1 && c2)
        if is_cheap_constant(def) {
            return true;
        }

        // For other expressions, must be used exactly once
        let use_count = self.use_counts.get(name).copied().unwrap_or(0);
        if use_count != 1 {
            return false;
        }

        // Check if the name is a generated temp name (tN pattern)
        let is_generated_name = is_generated_temp_name(name);

        // For user-named vars, only inline constants and simple variable refs
        // For generated vars, be more aggressive
        if is_generated_name {
            is_inlinable_for_generated(def)
        } else {
            is_inlinable_for_named(def)
        }
    }

    /// Get the expression to inline for a variable, if applicable
    pub fn get_inline_expr(&self, name: &str) -> Option<&Expression> {
        if self.should_inline(name) {
            self.definitions.get(name)
        } else {
            None
        }
    }

    /// Get all variables that should be inlined
    pub fn inlinable_vars(&self) -> Vec<String> {
        self.use_counts.keys()
            .filter(|name| self.should_inline(name))
            .cloned()
            .collect()
    }

}

/// Check if a name is a generated temp name like "t0", "t123", "tmp__1"
fn is_generated_temp_name(name: &str) -> bool {
    // Pattern: t followed by digits
    if name.starts_with('t') && name.len() > 1 && name[1..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    // Pattern: tmp__ followed by anything
    if name.starts_with("tmp__") {
        return true;
    }
    false
}

/// Check if an expression is a cheap constant that should always be inlined
/// regardless of use count. This is important for boolean constants that
/// appear in short-circuit patterns like `if c1 then c2 else false`.
fn is_cheap_constant(expr: &Expression) -> bool {
    matches!(expr, Expression::Constant(ConstantValue::Bool(_)))
}

/// Check if expression is inlinable for a user-named var (conservative)
fn is_inlinable_for_named(expr: &Expression) -> bool {
    matches!(expr, Expression::Constant(_) | Expression::Var(_))
}

/// Check if expression is inlinable for a generated var (aggressive)
/// Monadic subexpressions get wrapped with (← ...) by the renderer.
fn is_inlinable_for_generated(expr: &Expression) -> bool {
    match expr {
        // Constants are always inlinable
        Expression::Constant(_) => true,
        // Simple variable refs can be inlined
        Expression::Var(_) => true,
        // Binary ops are inlinable - monadic operands get (← ...) wrapper
        Expression::BinOp { .. } => true,
        // Unary ops are inlinable - monadic operand gets (← ...) wrapper
        Expression::UnOp { .. } => true,
        // Cast expressions are inlinable - monadic value gets (← ...) wrapper
        Expression::Cast { .. } => true,
        // Field access is inlinable - monadic operand gets (← ...) wrapper
        Expression::FieldAccess { .. } => true,
        // Pack expressions are inlinable - monadic fields get (← ...) wrapper
        Expression::Pack { .. } => true,
        // Tuples are inlinable - monadic elements get (← ...) wrapper
        Expression::Tuple(_) => true,
        // Vector ops are inlinable - monadic operands get (← ...) wrapper
        Expression::VecOp { .. } => true,
        // All function calls are inlinable - monadic calls are rendered with (← ...) syntax
        Expression::Call { .. } => true,
        // Unpack is inlinable - monadic operand gets (← ...) wrapper
        Expression::Unpack { .. } => true,
        // If-expressions with no statements in blocks can be inlined
        Expression::IfExpr { then_block, else_block, .. } => {
            then_block.statements.is_empty() && else_block.statements.is_empty()
        }
        // While expressions are never inlinable (complex control flow)
        Expression::WhileExpr { .. } => false,
    }
}

/// Collect definitions and count uses at TOP LEVEL ONLY.
/// Does NOT recurse into IfExpr/WhileExpr blocks - those are separate scopes.
fn collect_definitions_and_uses_toplevel(
    stmt: &Statement,
    definitions: &mut BTreeMap<String, Expression>,
    use_counts: &mut BTreeMap<String, usize>,
    is_monadic: &mut BTreeMap<String, bool>,
) {
    match stmt {
        Statement::Sequence(stmts) => {
            for s in stmts {
                collect_definitions_and_uses_toplevel(s, definitions, use_counts, is_monadic);
            }
        }
        Statement::Let { pattern, value, types } => {
            // Record definitions for single-variable patterns
            if let LetPattern::Single(name) = pattern {
                definitions.insert(name.clone(), value.clone());
                // Track whether this definition is monadic
                let monadicity = types.iter().any(|ty| ty.is_monad()) || value.is_monadic();
                is_monadic.insert(name.clone(), monadicity);
            }
            // Count uses in the value expression but NOT recursing into blocks
            count_uses_toplevel(value, use_counts);
        }
        Statement::Return { values } => {
            for expr in values {
                count_uses_toplevel(expr, use_counts);
            }
        }
        Statement::Abort { code } => {
            count_uses_toplevel(code, use_counts);
        }
        Statement::UpdateField { target, new_value, .. } => {
            count_uses_toplevel(target, use_counts);
            count_uses_toplevel(new_value, use_counts);
        }
        Statement::UpdateVectorElement { target, index, new_value } => {
            count_uses_toplevel(target, use_counts);
            count_uses_toplevel(index, use_counts);
            count_uses_toplevel(new_value, use_counts);
        }
        Statement::Requires { condition } | Statement::Ensures { condition } => {
            count_uses_toplevel(condition, use_counts);
        }
    }
}

/// Count uses of variables at the current scope level.
/// Does NOT recurse into IfExpr/WhileExpr blocks - those have their own scope.
fn count_uses_toplevel(expr: &Expression, use_counts: &mut BTreeMap<String, usize>) {
    match expr {
        Expression::Var(name) => {
            *use_counts.entry(name.clone()).or_insert(0) += 1;
        }
        Expression::BinOp { lhs, rhs, .. } => {
            count_uses_toplevel(lhs, use_counts);
            count_uses_toplevel(rhs, use_counts);
        }
        Expression::UnOp { operand, .. } => {
            count_uses_toplevel(operand, use_counts);
        }
        Expression::Cast { value, .. } => {
            count_uses_toplevel(value, use_counts);
        }
        Expression::FieldAccess { operand, .. } => {
            count_uses_toplevel(operand, use_counts);
        }
        Expression::Unpack { operand, .. } => {
            count_uses_toplevel(operand, use_counts);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                count_uses_toplevel(arg, use_counts);
            }
        }
        Expression::Pack { fields, .. } => {
            for field in fields {
                count_uses_toplevel(field, use_counts);
            }
        }
        Expression::VecOp { operands, .. } => {
            for op in operands {
                count_uses_toplevel(op, use_counts);
            }
        }
        Expression::Tuple(exprs) => {
            for e in exprs {
                count_uses_toplevel(e, use_counts);
            }
        }
        // For IfExpr/WhileExpr, only count uses at top level (condition, initial, result)
        // but NOT inside the block statements - those are separate scopes
        Expression::IfExpr { condition, then_block, else_block } => {
            count_uses_toplevel(condition, use_counts);
            // Only count uses in results, not in statements
            count_uses_toplevel(&then_block.result, use_counts);
            count_uses_toplevel(&else_block.result, use_counts);
        }
        Expression::WhileExpr { condition, body } => {
            // Only count uses in results, not in statements
            count_uses_toplevel(&condition.result, use_counts);
            count_uses_toplevel(&body.result, use_counts);
            // State variables from body.result are also used (they reference outer scope)
            for var in body.result.iter_vars() {
                *use_counts.entry(var.to_string()).or_insert(0) += 1;
            }
        }
        Expression::Constant(_) => {}
    }
}

/// Apply variable inlining to a statement tree
pub fn inline_temps(stmt: Statement, info: &TempUsageInfo) -> Statement {
    // Create substitution map for inlinable vars
    let mut inlinable: BTreeMap<String, Expression> = info.inlinable_vars()
        .into_iter()
        .filter_map(|name| info.definitions.get(&name).map(|e| (name, e.clone())))
        .collect();

    if inlinable.is_empty() {
        return stmt;
    }

    // Recursively inline vars within the replacement expressions themselves
    // This handles chains like: t10 := t8 != t9, where t8 and t9 should also be inlined
    // We iterate until no more changes (fixpoint)
    loop {
        let mut changed = false;
        let names: Vec<_> = inlinable.keys().cloned().collect();
        for name in names {
            let expr = inlinable.get(&name).unwrap().clone();
            let new_expr = inline_vars_in_expr_only(expr.clone(), &inlinable);
            if !expressions_equal(&expr, &new_expr) {
                inlinable.insert(name, new_expr);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Transform the statement tree
    inline_vars_in_stmt(stmt, &inlinable)
}

/// Check if two expressions are structurally equal (for fixpoint detection)
fn expressions_equal(a: &Expression, b: &Expression) -> bool {
    // Simple structural comparison - could be improved
    format!("{:?}", a) == format!("{:?}", b)
}

/// Inline vars in an expression without recursing into nested statement blocks.
/// This is used for the fixpoint loop to inline vars within replacement expressions.
fn inline_vars_in_expr_only(expr: Expression, inlinable: &BTreeMap<String, Expression>) -> Expression {
    match expr {
        Expression::Var(name) => {
            if let Some(replacement) = inlinable.get(&name) {
                replacement.clone()
            } else {
                Expression::Var(name)
            }
        }
        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(inline_vars_in_expr_only(*lhs, inlinable)),
            rhs: Box::new(inline_vars_in_expr_only(*rhs, inlinable)),
        },
        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(inline_vars_in_expr_only(*operand, inlinable)),
        },
        Expression::Cast { target_type, value } => Expression::Cast {
            target_type,
            value: Box::new(inline_vars_in_expr_only(*value, inlinable)),
        },
        Expression::FieldAccess { operand, struct_id, field_index } => Expression::FieldAccess {
            operand: Box::new(inline_vars_in_expr_only(*operand, inlinable)),
            struct_id,
            field_index,
        },
        Expression::Unpack { operand, struct_id } => Expression::Unpack {
            operand: Box::new(inline_vars_in_expr_only(*operand, inlinable)),
            struct_id,
        },
        Expression::Call { function, type_args, args, convention } => Expression::Call {
            function,
            type_args,
            args: args.into_iter().map(|a| inline_vars_in_expr_only(a, inlinable)).collect(),
            convention,
        },
        Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(|f| inline_vars_in_expr_only(f, inlinable)).collect(),
        },
        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(|o| inline_vars_in_expr_only(o, inlinable)).collect(),
        },
        Expression::Tuple(exprs) => Expression::Tuple(
            exprs.into_iter().map(|e| inline_vars_in_expr_only(e, inlinable)).collect()
        ),
        // Don't recurse into IfExpr/WhileExpr blocks - those are handled by statement inlining
        Expression::IfExpr { .. } | Expression::WhileExpr { .. } => expr,
        Expression::Constant(_) => expr,
    }
}

/// Recursively inline vars in a statement
fn inline_vars_in_stmt(stmt: Statement, inlinable: &BTreeMap<String, Expression>) -> Statement {
    match stmt {
        Statement::Sequence(stmts) => {
            let new_stmts: Vec<Statement> = stmts.into_iter()
                .filter_map(|s| {
                    // Skip Let statements that define inlinable vars
                    if let Statement::Let { pattern: LetPattern::Single(name), .. } = &s {
                        if inlinable.contains_key(name) {
                            return None;
                        }
                    }
                    Some(inline_vars_in_stmt(s, inlinable))
                })
                .collect();
            Statement::Sequence(new_stmts)
        }
        Statement::Let { pattern, value, types } => {
            // Skip if this is an inlinable definition (handled by Sequence case)
            Statement::Let {
                pattern,
                value: inline_vars_in_expr(value, inlinable),
                types,
            }
        }
        Statement::Return { values } => Statement::Return {
            values: values.into_iter()
                .map(|e| inline_vars_in_expr(e, inlinable))
                .collect(),
        },
        Statement::Abort { code } => Statement::Abort {
            code: inline_vars_in_expr(code, inlinable),
        },
        Statement::UpdateField { target, struct_id, field_index, new_value } => Statement::UpdateField {
            target: inline_vars_in_expr(target, inlinable),
            struct_id,
            field_index,
            new_value: inline_vars_in_expr(new_value, inlinable),
        },
        Statement::UpdateVectorElement { target, index, new_value } => Statement::UpdateVectorElement {
            target: inline_vars_in_expr(target, inlinable),
            index: inline_vars_in_expr(index, inlinable),
            new_value: inline_vars_in_expr(new_value, inlinable),
        },
        Statement::Requires { condition } => Statement::Requires {
            condition: inline_vars_in_expr(condition, inlinable),
        },
        Statement::Ensures { condition } => Statement::Ensures {
            condition: inline_vars_in_expr(condition, inlinable),
        },
    }
}

/// Inline vars in an expression, including removing inlined Let definitions from nested blocks
fn inline_vars_in_expr(expr: Expression, inlinable: &BTreeMap<String, Expression>) -> Expression {
    match expr {
        Expression::Var(ref name) => {
            if let Some(replacement) = inlinable.get(name) {
                // The replacement expression may contain Var references to other inlinable vars
                // (e.g., IfExpr with Var("t9") in its condition).
                // We need to recursively inline those as well.
                //
                // NOTE: This could cause infinite recursion if there's a cycle (a -> b -> a).
                // However, the analysis should prevent cycles since a var can only use vars
                // defined before it in the same scope.
                inline_vars_in_expr(replacement.clone(), inlinable)
            } else {
                expr
            }
        }
        Expression::IfExpr { condition, then_block, else_block } => Expression::IfExpr {
            condition: Box::new(inline_vars_in_expr(*condition, inlinable)),
            then_block: inline_vars_in_block(then_block, inlinable, &[]),
            else_block: inline_vars_in_block(else_block, inlinable, &[]),
        },
        Expression::WhileExpr { condition, body } => {
            // Variables used in the body result expression should NOT be inlined -
            // they represent the loop state returned from each iteration.
            // Without this, assignments like `let r := (loop_r * loop_r) >>> 63` would
            // be inlined into the result tuple `(f, r, log_2_x32, shift)`, removing the
            // Let statements that perform the actual loop computation.
            let mut protected: Vec<String> = Vec::new();
            for var_name in body.result.iter_vars() {
                if !protected.contains(&var_name.to_string()) {
                    protected.push(var_name.to_string());
                }
            }

            let protected_refs: Vec<&str> = protected.iter().map(|s| s.as_str()).collect();
            Expression::WhileExpr {
                condition: inline_vars_in_block(condition, inlinable, &protected_refs),
                body: inline_vars_in_block(body, inlinable, &protected_refs),
            }
        }
        Expression::BinOp { op, lhs, rhs } => Expression::BinOp {
            op,
            lhs: Box::new(inline_vars_in_expr(*lhs, inlinable)),
            rhs: Box::new(inline_vars_in_expr(*rhs, inlinable)),
        },
        Expression::UnOp { op, operand } => Expression::UnOp {
            op,
            operand: Box::new(inline_vars_in_expr(*operand, inlinable)),
        },
        Expression::Cast { value, target_type } => Expression::Cast {
            value: Box::new(inline_vars_in_expr(*value, inlinable)),
            target_type,
        },
        Expression::FieldAccess { struct_id, field_index, operand } => Expression::FieldAccess {
            struct_id,
            field_index,
            operand: Box::new(inline_vars_in_expr(*operand, inlinable)),
        },
        Expression::Unpack { struct_id, operand } => Expression::Unpack {
            struct_id,
            operand: Box::new(inline_vars_in_expr(*operand, inlinable)),
        },
        Expression::Call { function, args, type_args, convention } => Expression::Call {
            function,
            args: args.into_iter().map(|e| inline_vars_in_expr(e, inlinable)).collect(),
            type_args,
            convention,
        },
        Expression::Pack { struct_id, type_args, fields } => Expression::Pack {
            struct_id,
            type_args,
            fields: fields.into_iter().map(|e| inline_vars_in_expr(e, inlinable)).collect(),
        },
        Expression::VecOp { op, operands } => Expression::VecOp {
            op,
            operands: operands.into_iter().map(|e| inline_vars_in_expr(e, inlinable)).collect(),
        },
        Expression::Tuple(exprs) => Expression::Tuple(
            exprs.into_iter().map(|e| inline_vars_in_expr(e, inlinable)).collect(),
        ),
        expr @ Expression::Constant(_) => expr,
    }
}

/// Inline vars in a block, removing inlined Let definitions
/// This handles scope-aware inlining: the block's own temps are analyzed
/// and inlined within the block's scope.
///
/// `protected_vars` - variable names that should NEVER be inlined in this block
/// (e.g., loop state variables in a while body that need their Let statements preserved)
fn inline_vars_in_block(block: Block, outer_inlinable: &BTreeMap<String, Expression>, protected_vars: &[&str]) -> Block {
    // First, analyze this block's scope to find temps that can be inlined within it
    let block_stmt = Statement::Sequence(block.statements.clone());
    let mut block_defs: BTreeMap<String, Expression> = BTreeMap::new();
    let mut block_uses: BTreeMap<String, usize> = BTreeMap::new();
    let mut block_monadic: BTreeMap<String, bool> = BTreeMap::new();
    collect_definitions_and_uses_toplevel(&block_stmt, &mut block_defs, &mut block_uses, &mut block_monadic);

    // Also count uses in the block result
    count_uses_toplevel(&block.result, &mut block_uses);

    // Build the block's own inlinable set, EXCLUDING protected variables
    let block_info = TempUsageInfo {
        use_counts: block_uses,
        definitions: block_defs,
        is_monadic: block_monadic,
    };
    let mut block_inlinable: BTreeMap<String, Expression> = block_info.inlinable_vars()
        .into_iter()
        .filter(|name| !protected_vars.contains(&name.as_str())) // Exclude protected vars
        .filter_map(|name| block_info.definitions.get(&name).map(|e| (name, e.clone())))
        .collect();

    // If we have block-local inlinables, apply fixpoint inlining to them
    if !block_inlinable.is_empty() {
        loop {
            let mut changed = false;
            let names: Vec<_> = block_inlinable.keys().cloned().collect();
            for name in names {
                let expr = block_inlinable.get(&name).unwrap().clone();
                let new_expr = inline_vars_in_expr_only(expr.clone(), &block_inlinable);
                if !expressions_equal(&expr, &new_expr) {
                    block_inlinable.insert(name, new_expr);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    // Merge outer scope inlinable with block-local (block takes precedence for shadowing)
    // IMPORTANT: Remove outer variables that are shadowed by protected vars (loop state vars)
    // This prevents trying to inline the outer definition when the inner scope has a shadow
    let mut combined_inlinable: BTreeMap<String, Expression> = outer_inlinable.iter()
        .filter(|(name, _)| !protected_vars.contains(&name.as_str()))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    combined_inlinable.extend(block_inlinable);

    // Apply inlining to statements
    let statements: Vec<Statement> = block.statements.into_iter()
        .filter_map(|s| {
            // Skip Let statements that define inlinable vars
            if let Statement::Let { pattern: LetPattern::Single(name), .. } = &s {
                if combined_inlinable.contains_key(name) {
                    return None;
                }
            }
            Some(inline_vars_in_stmt(s, &combined_inlinable))
        })
        .collect();

    Block {
        statements,
        result: Box::new(inline_vars_in_expr(*block.result, &combined_inlinable)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ConstantValue, TheoremType};
    use ethnum::U256;

    fn make_test_registry() -> VariableRegistry {
        VariableRegistry::new()
    }

    #[test]
    fn test_single_use_constant_inlined() {
        // let t1 := 42
        // let t2 := x + t1
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("t1".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Let {
                pattern: LetPattern::Single("t2".to_string()),
                value: Expression::BinOp {
                    op: crate::BinOp::Add,
                    lhs: Box::new(Expression::Var("x".to_string())),
                    rhs: Box::new(Expression::Var("t1".to_string())),
                },
                types: vec![TheoremType::UInt(32)],
            },
        ]);

        let registry = make_test_registry();
        let info = TempUsageInfo::analyze(&body, &registry);
        assert!(info.should_inline("t1"));
        assert!(!info.should_inline("x")); // x is used once but not defined in this scope
    }

    #[test]
    fn test_multi_use_not_inlined() {
        // let t1 := 42
        // let t2 := t1 + t1  -- t1 used twice
        let body = Statement::Sequence(vec![
            Statement::Let {
                pattern: LetPattern::Single("t1".to_string()),
                value: Expression::Constant(ConstantValue::UInt { bits: 32, value: U256::from(42u32) }),
                types: vec![TheoremType::UInt(32)],
            },
            Statement::Let {
                pattern: LetPattern::Single("t2".to_string()),
                value: Expression::BinOp {
                    op: crate::BinOp::Add,
                    lhs: Box::new(Expression::Var("t1".to_string())),
                    rhs: Box::new(Expression::Var("t1".to_string())),
                },
                types: vec![TheoremType::UInt(32)],
            },
        ]);

        let registry = make_test_registry();
        let info = TempUsageInfo::analyze(&body, &registry);
        assert!(!info.should_inline("t1")); // used twice
    }
}
