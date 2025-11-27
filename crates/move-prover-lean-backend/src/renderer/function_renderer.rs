// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use std::fmt::Write;
use intermediate_theorem_format::{TheoremFunction, TheoremProgram, TheoremType};
use super::type_renderer::type_to_string;
use super::statement_renderer::render_stmt;
use super::expression_renderer::RenderCtx;
use super::lean_writer::LeanWriter;
use crate::escape;

/// Render a function definition.
pub fn render_function<W: Write>(func: &TheoremFunction, program: &TheoremProgram, current_module_namespace: &str, w: &mut LeanWriter<W>) {
    let escaped_name = escape::escape_identifier(&func.name);

    // partial def name
    w.write("partial def ");
    w.write(&escaped_name);

    // Type parameters with constraints
    for tp in &func.signature.type_params {
        w.write(&format!(" ({} : Type)", tp));
        w.write(&format!(" [BEq {}]", tp));
        w.write(&format!(" [Inhabited {}]", tp));
    }

    // Parameters
    for p in &func.signature.parameters {
        let param_name = if p.name.is_empty() || p.name == "_" {
            panic!("BUG: Parameter has empty or underscore name");
        } else {
            escape::escape_identifier(&p.name)
        };
        let type_str = type_to_string(&p.param_type, &program.name_manager, Some(current_module_namespace));
        w.write(&format!(" ({} : {})", param_name, type_str));
    }

    // Return type
    let return_type = compute_return_type(&func.signature.return_types);
    w.write(" : ");
    match &return_type {
        TheoremType::Except(_) => {
            let type_str = type_to_string(&return_type, &program.name_manager, Some(current_module_namespace));
            w.write(&type_str);
        }
        _ => {
            let type_str = type_to_string(&return_type, &program.name_manager, Some(current_module_namespace));
            w.write(&format!("(Except AbortCode {})", type_str));
        }
    }
    w.write(" :=\n");

    // Function body
    w.write("  do\n");
    w.indent();
    w.indent();

    let ctx = RenderCtx {
        registry: &func.ssa_registry,
        program,
        current_module_id: func.module_id,
        current_module_namespace: Some(current_module_namespace),
    };
    render_stmt(&func.body, &ctx, w);

    w.dedent();
    w.dedent();
    w.write("\n");
}

/// Compute return type from signature return types.
fn compute_return_type(return_types: &[TheoremType]) -> TheoremType {
    if return_types.is_empty() {
        TheoremType::Tuple(vec![])
    } else if return_types.len() == 1 {
        return_types[0].clone()
    } else {
        TheoremType::Tuple(return_types.to_vec())
    }
}
