// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremType to Lean syntax.
//! Pure translation - no logic, just pattern matching.

use std::fmt::Write;
use intermediate_theorem_format::{TheoremType, NameManager};
use crate::escape;

/// Render a type to Lean syntax.
pub fn render_type<W: Write>(ty: &TheoremType, names: &NameManager, current_module: Option<&str>, w: &mut W) {
    match ty {
        TheoremType::Bool => write!(w, "Bool").unwrap(),
        TheoremType::UInt(8) => write!(w, "UInt8").unwrap(),
        TheoremType::UInt(16) => write!(w, "UInt16").unwrap(),
        TheoremType::UInt(32) => write!(w, "UInt32").unwrap(),
        TheoremType::UInt(64) => write!(w, "UInt64").unwrap(),
        TheoremType::UInt(128) => write!(w, "UInt128").unwrap(),
        TheoremType::UInt(256) => write!(w, "UInt256").unwrap(),
        TheoremType::UInt(width) => write!(w, "UInt{}", width).unwrap(),
        TheoremType::SInt(width) => write!(w, "Int{}", width).unwrap(),
        TheoremType::Address => write!(w, "Address").unwrap(),

        TheoremType::Struct { struct_id, type_args } => {
            let struct_names = names.get_struct_names(*struct_id);
            let escaped_name = escape::escape_struct_name(&struct_names.type_name);

            // Don't qualify Lean built-in types
            let qualified_name = if escape::is_lean_builtin(&struct_names.type_name) {
                escaped_name
            } else {
                let namespace = escape::module_name_to_namespace(&struct_names.module_name);
                // Don't qualify if we're in the same module
                if current_module == Some(namespace.as_str()) {
                    escaped_name
                } else {
                    format!("{}.{}", namespace, escaped_name)
                }
            };

            if type_args.is_empty() {
                write!(w, "{}", qualified_name).unwrap();
            } else {
                write!(w, "({}", qualified_name).unwrap();
                for arg in type_args {
                    write!(w, " ").unwrap();
                    render_type(arg, names, current_module, w);
                }
                write!(w, ")").unwrap();
            }
        }

        TheoremType::Vector(elem) => {
            write!(w, "(List ").unwrap();
            render_type(elem, names, current_module, w);
            write!(w, ")").unwrap();
        }

        // References are erased in pure functional Lean
        TheoremType::Reference(inner) | TheoremType::MutableReference(inner) => {
            render_type(inner, names, current_module, w);
        }

        TheoremType::TypeParameter(idx) => {
            write!(w, "tv{}", idx).unwrap();
        }

        TheoremType::Tuple(types) => {
            if types.is_empty() {
                write!(w, "Unit").unwrap();
            } else if types.len() == 1 {
                render_type(&types[0], names, current_module, w);
            } else {
                write!(w, "(").unwrap();
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        write!(w, " × ").unwrap();
                    }
                    render_type(ty, names, current_module, w);
                }
                write!(w, ")").unwrap();
            }
        }

        TheoremType::Except(inner) => {
            write!(w, "(Except AbortCode ").unwrap();
            render_type(inner, names, current_module, w);
            write!(w, ")").unwrap();
        }
    }
}

/// Render a type to a string.
pub fn type_to_string(ty: &TheoremType, names: &NameManager, current_module: Option<&str>) -> String {
    let mut s = String::new();
    render_type(ty, names, current_module, &mut s);
    s
}

/// Get the Lean type name for a UInt width (e.g., 64 -> "UInt64").
pub fn uint_type_name(bits: usize) -> &'static str {
    match bits {
        8 => "UInt8",
        16 => "UInt16",
        32 => "UInt32",
        64 => "UInt64",
        128 => "UInt128",
        256 => "UInt256",
        _ => panic!("Unsupported UInt width: {}", bits),
    }
}

/// Get the Lean conversion function name for a UInt width (e.g., 64 -> "toUInt64").
pub fn uint_cast_func(bits: usize) -> &'static str {
    match bits {
        8 => "toUInt8",
        16 => "toUInt16",
        32 => "toUInt32",
        64 => "toUInt64",
        128 => "toUInt128",
        256 => "toUInt256",
        _ => panic!("Unsupported UInt width for cast: {}", bits),
    }
}
