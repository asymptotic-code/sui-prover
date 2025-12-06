// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use intermediate_theorem_format::{Function, Program};
use std::fmt::Write;

use super::context::RenderCtx;
use super::lean_writer::LeanWriter;
use super::render;
use super::type_renderer::type_to_string;
use crate::escape;

/// Check if a function is a spec function (requires, ensures, or aborts predicate)
fn is_spec_function(name: &str) -> bool {
    name.contains(".requires") || name.contains(".ensures") || name.contains(".aborts")
}

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

    // Return type - spec functions (requires, ensures, aborts) return Prop
    writer.write(" : ");
    if is_spec_function(&func.name) && matches!(func.signature.return_type, intermediate_theorem_format::Type::Bool) {
        writer.write("Prop");
    } else {
        let type_str = type_to_string(
            &func.signature.return_type,
            program,
            Some(current_module_namespace),
        );
        writer.write(&type_str);
    }
    writer.write(" :=\n");

    // Function body (strip requires/ensures nodes - they go in Specs/)
    writer.write("  ");
    writer.indent();

    let body = func.body.clone().simplify_blocks();

    // Check if body is empty block and return type is not unit - use sorry
    let body_is_empty = matches!(&body, intermediate_theorem_format::IRNode::Block { children } if children.is_empty());
    let return_type_is_unit = matches!(&func.signature.return_type, intermediate_theorem_format::Type::Tuple(v) if v.is_empty())
        || (func.signature.return_type.is_monad()
            && matches!(func.signature.return_type.unwrap_monad(), Some(intermediate_theorem_format::Type::Tuple(v)) if v.is_empty()));

    if body_is_empty && !return_type_is_unit {
        // Native function with no implementation - use sorry
        writer.write("sorry");
    } else if body_is_empty && return_type_is_unit {
        // Empty body returning unit - render ()
        writer.write("()");
    } else {
        // Note: Even spec functions use Bool operations in their body.
        // The Bool result is coerced to Prop by Lean's type system.
        let mut ctx = RenderCtx::new(
            program,
            &func.variables,
            func.module_id,
            Some(current_module_namespace),
            writer,
        );

        // If function is monadic and body isn't already a do block, wrap it
        if is_monadic {
            // Check if body already starts with do (Block node that contains monadic operations)
            let needs_do_wrap = match &body {
                intermediate_theorem_format::IRNode::Block { .. } => {
                    // Block will handle its own do wrapping if needed
                    false
                }
                _ => {
                    // For non-block nodes, check if they contain monadic calls
                    body.contains_monadic(&|fid| {
                        program.functions.get(fid).signature.return_type.is_monad()
                    })
                }
            };

            if needs_do_wrap {
                ctx.write("do\n");
                ctx.indent();
                render::render_monadic(&body, &mut ctx);
                ctx.dedent();
            } else {
                render::render(&body, &mut ctx);
            }
        } else {
            render::render(&body, &mut ctx);
        }

        writer = ctx.into_writer();
    }

    writer.dedent();
    writer.write("\n");

    writer
}
