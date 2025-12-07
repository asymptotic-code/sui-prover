// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use intermediate_theorem_format::{Function, FunctionID, IRNode, Program, Type};
use std::fmt::Write;

use super::context::RenderCtx;
use super::lean_writer::LeanWriter;
use super::render;
use super::type_renderer::type_to_string;
use crate::escape;

/// Render a function definition.
pub fn render_function<W: Write>(
    func_id: FunctionID,
    func: &Function,
    program: &Program,
    current_module_namespace: &str,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    let escaped_name = escape::escape_identifier(&func.full_name(func_id.variant));

    // def name (removed 'partial' to allow theorem proving)
    w.write("def ");
    w.write(&escaped_name);

    // Type parameters with constraints
    render_type_params(&func.signature.type_params, &mut w);

    // Parameters - collect Bool params for Decidable constraints
    let mut bool_params = Vec::new();
    for p in &func.signature.parameters {
        let param_name = if p.name.is_empty() || p.name == "_" {
            panic!("BUG: Parameter has empty or underscore name");
        } else {
            escape::escape_identifier(&p.name)
        };
        let type_str = type_to_string(&p.param_type, program, Some(current_module_namespace));
        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");

        // Track Bool params - they need Decidable constraints for if-then-else
        if matches!(p.param_type, Type::Bool) {
            bool_params.push(param_name);
        }
    }

    // Add Decidable constraints for Bool (Prop) parameters
    for param_name in &bool_params {
        w.write(" [Decidable ");
        w.write(param_name);
        w.write("]");
    }

    // Return type - spec functions (requires, ensures, aborts) return Prop
    w.write(" : ");
    if func_id.variant.returns_bool() && matches!(func.signature.return_type, Type::Bool) {
        w.write("Prop");
    } else {
        let type_str = type_to_string(
            &func.signature.return_type,
            program,
            Some(current_module_namespace),
        );
        w.write(&type_str);
    }
    w.line(" :=");

    // Function body (strip requires/ensures nodes - they go in Specs/)
    w.indent(false);

    let body = func.body.clone().simplify_blocks();

    // Check if body is empty block and return type is not unit - use sorry
    let body_is_empty = matches!(&body, IRNode::Block { children } if children.is_empty());
    let return_type_is_unit = matches!(&func.signature.return_type, Type::Tuple(v) if v.is_empty())
        || (func.signature.return_type.is_monad()
            && matches!(func.signature.return_type.unwrap_monad(), Some(Type::Tuple(v)) if v.is_empty()));

    // Track if body is sorry (can't derive Decidable from sorry)
    let body_is_sorry = body_is_empty && !return_type_is_unit;

    if body_is_sorry {
        // Native function with no implementation - use sorry
        w.write("sorry");
    } else if body_is_empty && return_type_is_unit {
        // Empty body returning unit - render ()
        w.write("()");
    } else {
        // Note: Even spec functions use Bool operations in their body.
        // The Bool result is coerced to Prop by Lean's type system.
        let mut ctx = RenderCtx::new(
            program,
            &func.variables,
            func.module_id,
            Some(current_module_namespace),
            w,
        );

        // Wrap non-Block bodies in a Block so Block handles do-notation uniformly
        let body_to_render = match &body {
            IRNode::Block { .. } => body.clone(),
            _ => IRNode::Block {
                children: vec![body.clone()],
            },
        };
        render::render(&body_to_render, &mut ctx);

        w = ctx.into_writer();
    }

    w.dedent(false);
    w.newline();

    // Add Decidable instance for Prop-returning functions (Bool renders as Prop in Lean)
    // Skip if body is sorry - can't derive Decidable from sorry
    if matches!(func.signature.return_type, Type::Bool) && !body_is_sorry {
        w.newline();
        render_decidable_instance(func, &escaped_name, program, current_module_namespace, &mut w);
    }

    w
}

/// Render type parameters with constraints: `(T : Type) [BEq T] [Inhabited T]`
fn render_type_params<W: Write>(type_params: &[String], w: &mut LeanWriter<W>) {
    for tp in type_params {
        w.write(" (");
        w.write(tp);
        w.write(" : Type) [BEq ");
        w.write(tp);
        w.write("] [Inhabited ");
        w.write(tp);
        w.write("]");
    }
}

/// Render a Decidable instance for a Prop-returning function
fn render_decidable_instance<W: Write>(
    func: &Function,
    escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    w: &mut LeanWriter<W>,
) {
    w.write("instance");

    // Type parameters with constraints
    render_type_params(&func.signature.type_params, w);

    // Value parameters
    for p in &func.signature.parameters {
        let param_name = escape::escape_identifier(&p.name);
        let type_str = type_to_string(&p.param_type, program, Some(current_module_namespace));
        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");
    }

    w.write(" : Decidable (");
    w.write(escaped_name);

    // Type arguments
    for tp in &func.signature.type_params {
        w.write(" ");
        w.write(tp);
    }

    // Value arguments
    for p in &func.signature.parameters {
        w.write(" ");
        w.write(&escape::escape_identifier(&p.name));
    }

    // Collect all functions that need to be unfolded for Decidable inference
    // This includes any function that returns a type containing Bool/Prop
    let unfold_names = collect_unfold_targets(&func.body, program, current_module_namespace);

    w.write(") := by unfold ");
    w.write(escaped_name);
    for name in &unfold_names {
        w.write(" ");
        w.write(name);
    }
    w.line("; infer_instance");
}

/// Collect function names that need to be unfolded for Decidable instance derivation.
/// We need to unfold any function whose return type contains Bool (rendered as Prop),
/// because Lean can't see through function calls to derive Decidable.
fn collect_unfold_targets(
    body: &IRNode,
    program: &Program,
    current_module_namespace: &str,
) -> Vec<String> {
    use std::collections::HashSet;

    let mut targets = Vec::new();
    let mut visited = HashSet::new();

    // Collect all function calls in the body
    for func_id in body.calls() {
        collect_unfold_targets_recursive(
            func_id,
            program,
            current_module_namespace,
            &mut targets,
            &mut visited,
        );
    }

    targets
}

/// Recursively collect unfold targets from a function and its callees
fn collect_unfold_targets_recursive(
    func_id: FunctionID,
    program: &Program,
    current_module_namespace: &str,
    targets: &mut Vec<String>,
    visited: &mut std::collections::HashSet<FunctionID>,
) {
    if visited.contains(&func_id) {
        return;
    }
    visited.insert(func_id);

    let func = program.functions.get(&func_id);
    let return_type = &func.signature.return_type;

    // Only unfold if the return type contains Bool (which becomes Prop in Lean)
    if !return_type.contains_bool() {
        return;
    }

    // Generate the fully qualified name for this function
    let func_name = if func.module_id == program.modules.iter().find(|(_, m)| {
        escape::module_name_to_namespace(&m.name) == current_module_namespace
    }).map(|(id, _)| *id).unwrap_or(usize::MAX) {
        escape::escape_identifier(&func.full_name(func_id.variant))
    } else {
        let module = program.modules.get(func.module_id);
        let namespace = escape::module_name_to_namespace(&module.name);
        format!(
            "{}.{}",
            namespace,
            escape::escape_identifier(&func.full_name(func_id.variant))
        )
    };

    targets.push(func_name);

    // Recursively check callees
    for callee_id in func.body.calls() {
        collect_unfold_targets_recursive(
            callee_id,
            program,
            current_module_namespace,
            targets,
            visited,
        );
    }
}
