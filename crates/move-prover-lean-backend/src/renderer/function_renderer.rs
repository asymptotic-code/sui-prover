// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use intermediate_theorem_format::{Function, Program};
use std::fmt::Write;

use super::ir_renderer::{render_block, RenderCtx};
use super::lean_writer::LeanWriter;
use super::type_renderer::type_to_string;
use crate::escape;

/// Render a function definition.
pub fn render_function<W: Write>(
    func: &Function,
    program: &Program,
    current_module_namespace: &str,
    w: LeanWriter<W>,
) -> LeanWriter<W> {
    let is_monadic = func.signature.return_type.is_monad();
    let escaped_name = escape::escape_identifier(&func.name);

    let mut writer = w;

    // def name (removed 'partial' to allow theorem proving)
    writer.write("def ");
    writer.write(&escaped_name);

    // Type parameters with constraints
    for tp in &func.signature.type_params {
        writer.write(&format!(" ({} : Type)", tp));
        writer.write(&format!(" [BEq {}]", tp));
        writer.write(&format!(" [Inhabited {}]", tp));
    }

    // Parameters
    for p in &func.signature.parameters {
        let param_name = if p.name.is_empty() || p.name == "_" {
            panic!("BUG: Parameter has empty or underscore name");
        } else {
            escape::escape_identifier(&p.name)
        };
        let type_str = type_to_string(&p.param_type, program, Some(current_module_namespace));
        writer.write(&format!(" ({} : {})", param_name, type_str));
    }

    // Return type
    writer.write(" : ");
    let type_str = type_to_string(
        &func.signature.return_type,
        program,
        Some(current_module_namespace),
    );
    writer.write(&type_str);
    writer.write(" :=\n");

    // Function body
    writer.write("  ");
    writer.indent();

    let mut ctx = RenderCtx::new(
        program,
        &func.variables,
        func.module_id,
        Some(current_module_namespace),
        writer,
    );

    render_block(&func.body, is_monadic, &mut ctx);

    let mut writer = ctx.into_writer();
    writer.dedent();
    writer.write("\n");

    writer
}
