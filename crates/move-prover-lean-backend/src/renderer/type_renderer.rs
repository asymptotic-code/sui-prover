// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremType to Lean syntax.
//! Pure translation - no logic, just pattern matching.

use super::context::RenderCtx;
use crate::escape;
use intermediate_theorem_format::{Program, Type};
use std::fmt::Write;

/// Render a type to Lean syntax.
pub fn render_type<W: Write>(ty: &Type, ctx: &mut RenderCtx<W>) {
    match ty {
        Type::Bool => {
            // Always use Prop for Bool - Lean backend only uses propositions
            ctx.write("Prop");
        }
        Type::UInt(8) => ctx.write("UInt8"),
        Type::UInt(16) => ctx.write("UInt16"),
        Type::UInt(32) => ctx.write("UInt32"),
        Type::UInt(64) => ctx.write("UInt64"),
        Type::UInt(128) => ctx.write("UInt128"),
        Type::UInt(256) => ctx.write("UInt256"),
        Type::UInt(width) => ctx.write(&format!("UInt{}", width)),
        Type::SInt(width) => ctx.write(&format!("Int{}", width)),
        Type::Address => ctx.write("Address"),

        Type::Struct {
            struct_id,
            type_args,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let module_def = ctx.program.modules.get(struct_def.module_id);
            let escaped_name = escape::escape_struct_name(&struct_def.name);

            // Don't qualify Lean built-in types
            let qualified_name = if escape::is_lean_builtin(&struct_def.name) {
                escaped_name
            } else {
                let namespace = escape::module_name_to_namespace(&module_def.name);
                // Don't qualify if we're in the same module
                if ctx.current_module_namespace == Some(namespace.as_str()) {
                    escaped_name
                } else {
                    format!("{}.{}", namespace, escaped_name)
                }
            };

            if type_args.is_empty() {
                ctx.write(&qualified_name);
            } else {
                ctx.write(&format!("({}", qualified_name));
                for arg in type_args {
                    ctx.write(" ");
                    render_type(arg, ctx);
                }
                ctx.write(")");
            }
        }

        Type::Vector(elem) => {
            ctx.write("(List ");
            render_type(elem, ctx);
            ctx.write(")");
        }

        // References are erased in pure functional Lean
        Type::Reference(inner) | Type::MutableReference(inner) => {
            render_type(inner, ctx);
        }

        Type::TypeParameter(idx) => {
            ctx.write(&format!("tv{}", idx));
        }

        Type::Tuple(types) => {
            if types.is_empty() {
                ctx.write("Unit");
            } else if types.len() == 1 {
                render_type(&types[0], ctx);
            } else {
                ctx.write("(");
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        ctx.write(" × ");
                    }
                    render_type(ty, ctx);
                }
                ctx.write(")");
            }
        }

        Type::Except(inner) => {
            ctx.write("(Except AbortCode ");
            render_type(inner, ctx);
            ctx.write(")");
        }
    }
}

/// Render a type to a string.
pub fn type_to_string(ty: &Type, program: &Program, current_module: Option<&str>) -> String {
    let mut s = String::new();
    use super::lean_writer::LeanWriter;
    use std::collections::BTreeMap;
    let writer = LeanWriter::new(&mut s);
    let registry = intermediate_theorem_format::VariableRegistry::new(BTreeMap::new());
    let mut ctx = RenderCtx::new(
        program,
        &registry,
        0, // ModuleID is just usize
        current_module,
        writer,
    );
    render_type(ty, &mut ctx);
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
pub fn uint_cast_func(bits: usize) -> String {
    format!("to{}", uint_type_name(bits))
}
