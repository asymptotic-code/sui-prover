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
            ctx.write("Bool");
        }
        Type::Prop => {
            ctx.write("Prop");
        }
        Type::UInt(width) => ctx.write(&format!("BoundedNat (2^{})", width)),
        Type::SInt(width) => {
            if *width == 0 {
                // SInt(0) is the unbounded mathematical integer type
                ctx.write("Int");
            } else {
                ctx.write(&format!("Int{}", width));
            }
        }
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
            } else if struct_def.name == "Real" && module_def.name == "real" {
                // Special case: Real from real module must be qualified as MoveReal.Real
                // to avoid ambiguity with Mathlib's Real (ℝ)
                "MoveReal.Real".to_string()
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
            // Use the actual type parameter name from the current function if available
            if let Some(type_params) = ctx.type_params {
                if let Some(name) = type_params.get(*idx as usize) {
                    ctx.write(name);
                } else {
                    // Fallback if index is out of bounds
                    ctx.write(&format!("tv{}", idx));
                }
            } else {
                // Fallback if no type params in context
                ctx.write(&format!("tv{}", idx));
            }
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
            ctx.write("(Except AbortCode (");
            render_type(inner, ctx);
            ctx.write("))");
        }
    }
}

/// Render a type to a string.
pub fn type_to_string(ty: &Type, program: &Program, current_module: Option<&str>) -> String {
    type_to_string_with_params(ty, program, current_module, None)
}

pub fn type_to_string_with_params(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
) -> String {
    type_to_string_full(ty, program, current_module, type_params, false)
}

pub fn type_to_string_full(
    ty: &Type,
    program: &Program,
    current_module: Option<&str>,
    type_params: Option<&[String]>,
    bool_as_prop: bool,
) -> String {
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
    if let Some(params) = type_params {
        ctx.with_type_params(params);
    }
    if bool_as_prop {
        ctx.with_bool_as_prop();
    }
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
