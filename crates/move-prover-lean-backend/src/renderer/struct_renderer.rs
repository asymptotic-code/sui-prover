// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremStruct to Lean structure definitions.

use super::lean_writer::LeanWriter;
use super::type_renderer::type_to_string;
use crate::escape;
use intermediate_theorem_format::{Program, Struct};
use std::fmt::Write;

/// Render a struct definition.
pub fn render_struct<W: Write>(
    struct_def: &Struct,
    program: &Program,
    current_module: &str,
    w: &mut LeanWriter<W>,
) {
    // Comment header
    w.write("-- Struct: ");
    w.line(&struct_def.qualified_name);

    // Structure declaration
    let struct_name = escape::escape_struct_name(&struct_def.name);
    w.write("structure ");
    w.write(&struct_name);

    // Universe variables for type parameters
    if !struct_def.type_params.is_empty() {
        w.write(".{");
        w.sep(
            ", ",
            (0..struct_def.type_params.len()).map(|i| format!("u{}", i)),
        );
        w.write("}");
    }

    // Type parameters
    for (i, type_param) in struct_def.type_params.iter().enumerate() {
        w.write(" (");
        w.write(type_param);
        w.write(" : Type u");
        w.write(&i.to_string());
        w.write(")");
    }

    w.line(" where");

    // Fields
    w.indent(false);
    for field in &struct_def.fields {
        let type_str = type_to_string(&field.field_type, program, Some(current_module));
        w.write(&escape::escape_identifier(&field.name));
        w.write(" : ");
        w.line(&type_str);
    }
    w.dedent(false);
    w.newline();
}
