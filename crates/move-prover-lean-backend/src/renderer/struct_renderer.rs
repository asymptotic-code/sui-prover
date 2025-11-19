// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Struct IR to Lean structure definitions

use intermediate_theorem_format::TheoremStruct;
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;
use crate::escape;

pub struct StructRenderer {
    type_renderer: TypeRenderer,
}

impl StructRenderer {
    pub fn new() -> Self {
        Self {
            type_renderer: TypeRenderer,
        }
    }

    /// Render a struct definition to a writer
    pub fn render(&self, struct_def: &TheoremStruct, writer: &LeanWriter) {
        // Comment header
        writer.emit(&format!("-- Struct: {}\n", struct_def.qualified_name));

        // Structure declaration with explicit universe polymorphism
        let struct_name = escape::escape_struct_name(&struct_def.name);
        writer.emit("structure ");
        writer.emit(&struct_name);

        // Add explicit universe variables if there are type parameters
        // This ensures proper universe level handling for recursive types
        if !struct_def.type_params.is_empty() {
            writer.emit(".{");
            for (i, _) in struct_def.type_params.iter().enumerate() {
                if i > 0 {
                    writer.emit(", ");
                }
                writer.emit(&format!("u{}", i));
            }
            writer.emit("}");
        }

        // Type parameters with universe levels
        if !struct_def.type_params.is_empty() {
            writer.emit(" ");
            for (i, type_param) in struct_def.type_params.iter().enumerate() {
                if i > 0 {
                    writer.emit(" ");
                }
                writer.emit(&format!("({} : Type u{})", type_param, i));
            }
        }

        writer.emit(" where\n");

        // Fields
        for field in &struct_def.fields {
            writer.emit("  ");
            writer.emit(&escape::escape_identifier(&field.name));
            writer.emit(" : ");
            self.type_renderer.render(&field.field_type, writer);
            writer.emit("\n");
        }

        writer.emit("\n");
    }
}
