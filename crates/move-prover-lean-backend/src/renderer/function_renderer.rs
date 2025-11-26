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

        // Render type parameters with their constraints
        // In Move's spec language, all types support equality and have default values
        // So we add BEq and Inhabited constraints to all type parameters
        if !func.signature.type_params.is_empty() {
            for tp in &func.signature.type_params {
                writer.emit(" (");
                writer.emit(tp);
                writer.emit(" : Type)");

                // Add BEq for equality comparisons (used in spec contexts)
                writer.emit(" [BEq ");
                writer.emit(tp);
                writer.emit("]");

                // Add Inhabited for fresh() calls and default values
                writer.emit(" [Inhabited ");
                writer.emit(tp);
                writer.emit("]");
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
        let return_type = self.compute_return_type(&func.signature.return_types);

        // All functions return ProgramState-wrapped values
        // But don't double-wrap if already wrapped
        writer.emit(" : ");
        match &return_type {
            intermediate_theorem_format::TheoremType::ProgramState(_) => {
                // Already wrapped, just render it
                self.type_renderer.render(&return_type, writer);
            }
            _ => {
                // Not wrapped yet, wrap it
                writer.emit("(ProgramState ");
                self.type_renderer.render(&return_type, writer);
                writer.emit(")");
            }
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

    /// Helper to compute return type from signature return types
    fn compute_return_type(&self, return_types: &[intermediate_theorem_format::TheoremType]) -> intermediate_theorem_format::TheoremType {
        use intermediate_theorem_format::TheoremType;

        if return_types.is_empty() {
            TheoremType::Tuple(vec![])
        } else if return_types.len() == 1 {
            return_types[0].clone()
        } else {
            TheoremType::Tuple(return_types.to_vec())
        }
    }
}
