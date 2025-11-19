// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremType to Lean syntax

use intermediate_theorem_format::TheoremType;
use crate::escape;
use super::lean_writer::LeanWriter;

pub struct TypeRenderer;

impl TypeRenderer {
    /// Render type to a writer
    pub fn render<'a>(&self, ty: &TheoremType, writer: &LeanWriter<'a>) {
        match ty {
            TheoremType::Bool => writer.emit("Bool"),
            TheoremType::UInt(8) => writer.emit("UInt8"),
            TheoremType::UInt(16) => writer.emit("UInt16"),
            TheoremType::UInt(32) => writer.emit("UInt32"),
            TheoremType::UInt(64) => writer.emit("UInt64"),
            TheoremType::UInt(128) => writer.emit("UInt128"),
            TheoremType::UInt(256) => writer.emit("UInt256"),
            TheoremType::UInt(width) => writer.emit(&format!("UInt{}", width)),
            TheoremType::SInt(width) => writer.emit(&format!("Int{}", width)),
            TheoremType::Address => writer.emit("Address"),
            TheoremType::Struct { struct_id, type_args } => {
                // Lookup names from NameManager
                let names = writer.name_manager.get_struct_names(*struct_id);
                let lean_name = &names.type_name;
                let module_name = &names.module_name;

                let escaped_name = escape::escape_struct_name(lean_name);

                // Don't qualify Lean built-in types (Option, etc.)
                let final_name = if escape::is_lean_builtin(lean_name) {
                    escaped_name
                } else {
                    // Capitalize module name for Lean namespace (matches program_renderer)
                    let namespace = escape::capitalize_first(module_name);

                    // If we're in the same module, don't qualify the name
                    if writer.current_module.as_ref().map(|s| s.as_str()) == Some(&namespace) {
                        escaped_name
                    } else {
                        // Qualify struct name with module namespace (e.g., Ecdsa_k1.KeyPair)
                        format!("{}.{}", namespace, escaped_name)
                    }
                };

                if type_args.is_empty() {
                    writer.emit(&final_name);
                } else {
                    writer.emit("(");
                    writer.emit(&final_name);
                    for arg in type_args {
                        writer.emit(" ");
                        self.render(arg, writer);
                    }
                    writer.emit(")");
                }
            }
            TheoremType::Vector(elem) => {
                writer.emit("(List ");
                self.render(elem, writer);
                writer.emit(")");
            }
            TheoremType::Reference(inner) => {
                // References are unwrapped in pure functional Lean
                self.render(inner, writer);
            }
            TheoremType::MutableReference(inner) => {
                // Mutable references are unwrapped in pure functional Lean
                self.render(inner, writer);
            }
            TheoremType::TypeParameter(idx) => {
                writer.emit(&format!("tv{}", idx));
            }
            TheoremType::Tuple(types) => {
                if types.is_empty() {
                    writer.emit("Unit");
                } else if types.len() == 1 {
                    self.render(&types[0], writer);
                } else {
                    writer.emit("(");
                    for (i, ty) in types.iter().enumerate() {
                        if i > 0 {
                            writer.emit(" × ");
                        }
                        self.render(ty, writer);
                    }
                    writer.emit(")");
                }
            }
            TheoremType::ProgramState(inner) => {
                writer.emit("(ProgramState ");
                self.render(inner, writer);
                writer.emit(")");
            }
        }
    }
}
