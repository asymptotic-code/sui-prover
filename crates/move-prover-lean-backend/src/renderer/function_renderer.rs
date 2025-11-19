// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax

use intermediate_theorem_format::{TheoremFunction, TheoremProgram, Statement};
use super::statement_renderer::StatementRenderer;
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;
use super::native_impls;
use crate::escape;

pub struct FunctionRenderer {
    type_renderer: TypeRenderer,
}

impl FunctionRenderer {
    pub fn new() -> Self {
        Self {
            type_renderer: TypeRenderer,
        }
    }


    /// Infer the actual return type from the function body
    /// Used when the signature doesn't match what the body actually returns
    fn infer_return_type_from_body(&self, func: &TheoremFunction) -> Option<String> {
        // Check if the body returns Unit (empty return or pure ())
        match &func.body {
            Statement::Sequence(stmts) => {
                if stmts.is_empty() {
                    return Some("Unit".to_string());
                }
                // Check the last statement
                if let Some(last) = stmts.last() {
                    match last {
                        Statement::Return { values } if values.is_empty() => {
                            return Some("Unit".to_string());
                        }
                        _ => {}
                    }
                }
            }
            Statement::Return { values } if values.is_empty() => {
                return Some("Unit".to_string());
            }
            _ => {}
        }
        None
    }

    /// Detect if function uses equality operations on type parameters
    fn uses_equality(&self, func: &TheoremFunction) -> bool {
        use intermediate_theorem_format::{Expression, BinOp};

        fn check_expr(expr: &Expression) -> bool {
            match expr {
                Expression::BinOp { op: BinOp::Eq, .. } |
                Expression::BinOp { op: BinOp::Neq, .. } => true,
                Expression::BinOp { lhs, rhs, .. } => check_expr(lhs) || check_expr(rhs),
                Expression::UnOp { operand, .. } => check_expr(operand),
                Expression::Call { args, .. } => args.iter().any(check_expr),
                Expression::Cast { value, .. } => check_expr(value),
                Expression::Pack { fields, .. } => fields.iter().any(check_expr),
                Expression::Unpack { operand, .. } | Expression::UnpackAll { operand, ..} => check_expr(operand),
                _ => false,
            }
        }

        fn check_stmt(stmt: &Statement) -> bool {
            match stmt {
                Statement::Sequence(stmts) => stmts.iter().any(check_stmt),
                Statement::Let { operation, .. } => check_expr(operation),
                Statement::If { then_branch, else_branch, .. } => {
                    check_stmt(then_branch) || check_stmt(else_branch)
                }
                Statement::While { condition, body, .. } => check_expr(condition) || check_stmt(body),
                _ => false,
            }
        }

        // Only relevant if function has type parameters
        if func.signature.type_params.is_empty() {
            return false;
        }

        check_stmt(&func.body)
    }

    /// Detect if function uses comparison operations on type parameters
    fn uses_comparisons(&self, func: &TheoremFunction) -> bool {
        use intermediate_theorem_format::{Expression, BinOp};

        fn check_expr(expr: &Expression) -> bool {
            match expr {
                Expression::BinOp { op: BinOp::Lt, .. } |
                Expression::BinOp { op: BinOp::Le, .. } |
                Expression::BinOp { op: BinOp::Gt, .. } |
                Expression::BinOp { op: BinOp::Ge, .. } => true,
                Expression::BinOp { lhs, rhs, .. } => check_expr(lhs) || check_expr(rhs),
                Expression::UnOp { operand, .. } => check_expr(operand),
                Expression::Call { args, .. } => args.iter().any(check_expr),
                Expression::Cast { value, .. } => check_expr(value),
                Expression::Pack { fields, .. } => fields.iter().any(check_expr),
                Expression::Unpack { operand, .. } | Expression::UnpackAll { operand, ..} => check_expr(operand),
                _ => false,
            }
        }

        fn check_stmt(stmt: &Statement) -> bool {
            match stmt {
                Statement::Sequence(stmts) => stmts.iter().any(check_stmt),
                Statement::Let { operation, .. } => check_expr(operation),
                Statement::If { then_branch, else_branch, .. } => {
                    check_stmt(then_branch) || check_stmt(else_branch)
                }
                Statement::While { condition, body, .. } => check_expr(condition) || check_stmt(body),
                _ => false,
            }
        }

        // Only relevant if function has type parameters
        if func.signature.type_params.is_empty() {
            return false;
        }

        check_stmt(&func.body)
    }

    pub fn render(&self, func: &TheoremFunction, program: &TheoremProgram, writer: &LeanWriter) {
        // Detect needed typeclass instances
        let needs_beq = self.uses_equality(func);
        let needs_ord = self.uses_comparisons(func);

        // Render function definition - use the function's actual name (escaped if needed)
        // Mark as partial to avoid termination checking issues
        let escaped_name = escape::escape_identifier(&func.name);
        writer.emit("partial def ");
        writer.emit(&escaped_name);

        // Render type parameters with typeclass constraints
        if !func.signature.type_params.is_empty() {
            for tp in &func.signature.type_params {
                writer.emit(" (");
                writer.emit(tp);
                writer.emit(" : Type)");
                if needs_beq {
                    writer.emit(" [BEq ");
                    writer.emit(tp);
                    writer.emit("]");
                }
                if needs_ord {
                    writer.emit(" [Ord ");
                    writer.emit(tp);
                    writer.emit("]");
                }
            }
        }

        // Render function parameters with sanitized and escaped parameter names
        for (idx, p) in func.signature.parameters.iter().enumerate() {
            // Extra validation: ensure parameter names are not empty or underscore-only
            let param_name = if p.name.is_empty() || p.name == "_" {
                format!("param{}", idx)
            } else {
                // Escape parameter names that conflict with Lean keywords
                escape::escape_identifier(&p.name)
            };
            writer.emit(" (");
            writer.emit(&param_name);
            writer.emit(" : ");
            self.type_renderer.render(&p.param_type, writer);
            writer.emit(")");
        }

        // Determine return type:
        // 1. Check for native override (vector operations)
        // 2. Infer from function body (spec functions that return ()) - but NOT for native functions
        // 3. Use signature (normal functions)

        // Check if this function has a native implementation registered
        // If so, we ALWAYS use the native impl, even if there's also a bytecode body
        let has_native_impl = program.get_module(func.module_id)
            .map(|module| native_impls::get_native_impl(&module.name, &func.name).is_some())
            .unwrap_or(false);

        // Compute return type as string (still needed for logic checks and stmt_renderer)
        let return_type = if let Some(module) = program.get_module(func.module_id) {
            // Check native override first
            if let Some(override_type) = native_impls::get_native_return_type_override(&module.name, &func.name) {
                override_type
            }
            // Then try to infer from body (only for non-native functions)
            else if !has_native_impl {
                if let Some(inferred_type) = self.infer_return_type_from_body(func) {
                    inferred_type
                } else {
                    self.compute_return_type_string(&func.signature.return_types, &program.name_manager)
                }
            }
            // Fall back to signature
            else {
                self.compute_return_type_string(&func.signature.return_types, &program.name_manager)
            }
        } else {
            self.compute_return_type_string(&func.signature.return_types, &program.name_manager)
        };

        // All functions return ProgramState-wrapped values
        // But don't double-wrap if already wrapped
        writer.emit(" : ");
        if return_type.starts_with("ProgramState ") || return_type.starts_with("(ProgramState ") {
            writer.emit(&return_type);
        } else {
            writer.emit("(ProgramState ");
            writer.emit(&return_type);
            writer.emit(")");
        }
        writer.emit(" :=\n");

        // If this function has a native implementation, use it and skip the bytecode body
        // This handles cases where Move provides both a native declaration AND a bytecode fallback
        if has_native_impl {
            if let Some(module) = program.get_module(func.module_id) {
                if let Some(native_impl) = native_impls::get_native_impl(&module.name, &func.name) {
                        // Use the native implementation from lemmas
                        // Native impls may not return ProgramState, so wrap in pure if needed
                        writer.emit("  pure ");

                        // Build call to native impl with all parameters
                        let mut call_args = Vec::new();

                        // Add type arguments
                        for tp in &func.signature.type_params {
                            call_args.push(tp.clone());
                        }

                        // Add value arguments (with escaped names)
                        for (idx, param) in func.signature.parameters.iter().enumerate() {
                            let param_name = if param.name.is_empty() || param.name == "_" {
                                format!("param{}", idx)
                            } else {
                                escape::escape_identifier(&param.name)
                            };
                            call_args.push(param_name);
                        }

                        if call_args.is_empty() {
                            writer.emit(&native_impl);
                        } else {
                            writer.emit("(");
                            writer.emit(&native_impl);
                            for arg in &call_args {
                                writer.emit(" ");
                                writer.emit(arg);
                            }
                            writer.emit(")");
                        }

                    writer.emit("\n\n");
                    return;
                }
            }
        }

        // Function body - start with indent level 1 (inside function)
        // Pass return type to help with abort type inference
        // All functions return ProgramState, so use 'do' notation
        writer.emit("  do\n");
        let mut stmt_renderer = StatementRenderer::with_return_type(return_type.clone());
        // Start with 2 levels of indentation (inside function's do-block)
        writer.indent();
        writer.indent();
        stmt_renderer.render(&func.body, &func.ssa_registry, program, writer);
        writer.unindent();
        writer.unindent();
        writer.emit("\n");
    }

    /// Helper to compute return type string from signature return types
    fn compute_return_type_string<'a>(&self, return_types: &[intermediate_theorem_format::TheoremType], name_manager: &'a intermediate_theorem_format::NameManager) -> String {
        if return_types.is_empty() {
            "Unit".to_string()
        } else if return_types.len() == 1 {
            let writer = LeanWriter::new(name_manager);
            self.type_renderer.render(&return_types[0], &writer);
            writer.extract_result()
        } else {
            let types = return_types.iter()
                .map(|t| {
                    let writer = LeanWriter::new(name_manager);
                    self.type_renderer.render(t, &writer);
                    writer.extract_result()
                })
                .collect::<Vec<_>>()
                .join(" × ");
            format!("({})", types)
        }
    }
}
