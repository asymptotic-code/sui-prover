// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax

use intermediate_theorem_format::{TheoremFunction, TheoremProgram};
use super::statement_renderer::StatementRenderer;
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;
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

    pub fn render(&self, func: &TheoremFunction, program: &TheoremProgram, writer: &LeanWriter) {
        // Render function definition - use the function's simple name (escaped if needed)
        // Mark as partial to avoid termination checking issues
        let escaped_name = escape::escape_identifier(&func.name);
        writer.emit("partial def ");
        writer.emit(&escaped_name);

        // Render type parameters (no typeclass constraints needed - Move doesn't support generic equality)
        if !func.signature.type_params.is_empty() {
            for tp in &func.signature.type_params {
                writer.emit(" (");
                writer.emit(tp);
                writer.emit(" : Type)");
            }
        }

        // Render function parameters with sanitized and escaped parameter names
        for p in func.signature.parameters.iter() {
            // Extra validation: ensure parameter names are not empty or underscore-only
            let param_name = if p.name.is_empty() || p.name == "_" {
                panic!("BUG: Parameter has empty or underscore name - IR should provide valid names");
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

        // Use signature return type (it's always correct - no inference needed)
        let return_type = self.compute_return_type_string(&func.signature.return_types, &program.name_manager);

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

        // Function body - start with indent level 1 (inside function)
        // Pass return type to help with abort type inference
        // All functions return ProgramState, so use 'do' notation
        writer.emit("  do\n");
        let mut stmt_renderer = StatementRenderer::with_return_type(return_type.clone());
        // Start with 2 levels of indentation (inside function's do-block)
        writer.indent();
        writer.indent();
        stmt_renderer.render(&func.body, &func.ssa_registry, program, func.module_id, writer);
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
