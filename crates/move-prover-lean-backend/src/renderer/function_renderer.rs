// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use std::fmt::Write;

use intermediate_theorem_format::{TheoremFunction, TheoremProgram};

use super::expression_renderer::RenderCtx;
use super::lean_writer::LeanWriter;
use super::statement_renderer::render_block;
use super::type_renderer::type_to_string;
use crate::escape;

/// Render a function definition.
pub fn render_function<W: Write>(func: &TheoremFunction, program: &TheoremProgram, current_module_namespace: &str, w: &mut LeanWriter<W>) {
    let is_monadic = func.signature.return_type.is_monad();
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
        let type_str = type_to_string(&p.param_type, program, Some(current_module_namespace));
        w.write(&format!(" ({} : {})", param_name, type_str));
    }

    // Return type
    w.write(" : ");
    let type_str = type_to_string(&func.signature.return_type, program, Some(current_module_namespace));
    w.write(&type_str);
    w.write(" :=\n");

    // Function body
    w.write("  ");
    w.indent();

    let ctx = RenderCtx {
        registry: &func.variables,
        program,
        current_module_id: func.module_id,
        current_module_namespace: Some(current_module_namespace),
        current_function_monadic: is_monadic,
    };

    render_block(&func.body, is_monadic, &ctx, w);

    w.dedent();
    w.write("\n");
}
