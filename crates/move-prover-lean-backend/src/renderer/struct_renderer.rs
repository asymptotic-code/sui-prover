// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremStruct to Lean structure definitions.

use super::lean_writer::LeanWriter;
use super::type_renderer::type_to_string;
use crate::escape;
use intermediate_theorem_format::{TheoremProgram, TheoremStruct};
use std::fmt::Write;

/// Render a struct definition.
pub fn render_struct<W: Write>(
    struct_def: &TheoremStruct,
    program: &TheoremProgram,
    current_module: &str,
    w: &mut LeanWriter<W>,
) {
    // Comment header
    w.line(&format!("-- Struct: {}", struct_def.qualified_name));

    // Structure declaration
    let struct_name = escape::escape_struct_name(&struct_def.name);
    w.write("structure ");
    w.write(&struct_name);

    // Universe variables for type parameters
    if !struct_def.type_params.is_empty() {
        w.write(".{");
        for (i, _) in struct_def.type_params.iter().enumerate() {
            if i > 0 {
                w.write(", ");
            }
            w.write(&format!("u{}", i));
        }
        w.write("}");
    }

    // Type parameters
    if !struct_def.type_params.is_empty() {
        w.write(" ");
        for (i, type_param) in struct_def.type_params.iter().enumerate() {
            if i > 0 {
                w.write(" ");
            }
            w.write(&format!("({} : Type u{})", type_param, i));
        }
    }

    w.line(" where");

    // Fields
    for field in &struct_def.fields {
        let type_str = type_to_string(&field.field_type, program, Some(current_module));
        w.write(&format!(
            "  {} : {}\n",
            escape::escape_identifier(&field.name),
            type_str
        ));
    }

    w.write("\n");
}
