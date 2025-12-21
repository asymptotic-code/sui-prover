// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use intermediate_theorem_format::{Const, Function, FunctionID, FunctionVariant, IRNode, Program, Type};
use std::collections::BTreeSet;
use std::fmt::Write;

use super::context::RenderCtx;
use super::lean_writer::LeanWriter;
use super::render;
use super::type_renderer::type_to_string;
use crate::escape;

/// Check if a function uses the Rat type (which is noncomputable in Lean with Real).
fn uses_rat_type(func: &Function, program: &Program, uses_rational: &std::collections::HashSet<FunctionID>) -> bool {
    // Check parameters
    for p in &func.signature.parameters {
        if type_contains_rat(&p.param_type, program) {
            return true;
        }
    }
    // Check return type
    if type_contains_rat(&func.signature.return_type, program) {
        return true;
    }
    // Check if function body calls any Real functions from rational module (transitive)
    if body_calls_rational_module_transitive(&func.body, uses_rational) {
        return true;
    }
    false
}

/// Recursively check if a type contains Real.
fn type_contains_rat(ty: &Type, program: &Program) -> bool {
    match ty {
        Type::Struct { struct_id, type_args } => {
            let struct_def = program.structs.get(*struct_id);
            // Check if this is the Real struct
            if struct_def.name == "Real" {
                return true;
            }
            // Check type arguments
            type_args.iter().any(|t| type_contains_rat(t, program))
        }
        Type::Tuple(types) => types.iter().any(|t| type_contains_rat(t, program)),
        Type::Vector(inner) => type_contains_rat(inner, program),
        Type::Reference(inner) | Type::MutableReference(inner) => type_contains_rat(inner, program),
        Type::Except(inner) => type_contains_rat(inner, program),
        _ => false,
    }
}

/// Compute the set of all functions that transitively use rational module or are native.
/// This is done once at the start to avoid infinite recursion and redundant computation.
fn compute_uses_rational_set(program: &Program) -> std::collections::HashSet<FunctionID> {
    let mut uses_rational = std::collections::HashSet::new();

    // First pass: identify direct users (rational module functions or natives)
    for (func_id, func) in program.functions.iter() {
        let module = program.modules.get(func.module_id);
        if module.name == "rational" || func.is_native() {
            uses_rational.insert(func_id);
        }
    }

    // Fixed-point iteration: propagate to callers
    let mut changed = true;
    while changed {
        changed = false;
        for (func_id, func) in program.functions.iter() {
            if uses_rational.contains(&func_id) {
                continue; // Already marked
            }
            // Check if this function calls any marked function
            let calls_marked = func.body.calls().any(|call_id| uses_rational.contains(&call_id));
            if calls_marked {
                uses_rational.insert(func_id);
                changed = true;
            }
        }
    }

    uses_rational
}

/// Check if the IR body calls any functions from the rational module (which are noncomputable).
/// Uses a precomputed set for O(1) lookups and avoids infinite recursion.
fn body_calls_rational_module_transitive(body: &IRNode, uses_rational: &std::collections::HashSet<FunctionID>) -> bool {
    body.calls().any(|func_id| uses_rational.contains(&func_id))
}

/// Check if a body ends with a non-Bool expression.
/// This detects malformed aborts bodies where the transformation failed to produce Bool.
///
/// IMPORTANT: This function is conservative - it only returns true for patterns that
/// are DEFINITELY non-Bool (like Pack, Field, Var at the end with no following expression).
/// Complex expressions with Ifs are assumed to be potentially correct.
fn body_ends_with_non_bool(body: &IRNode) -> bool {
    match body {
        // Bool literals are fine
        IRNode::Const(Const::Bool(_)) => false,

        // BinOp/UnOp are likely bool operations in abort predicates
        IRNode::BinOp { .. } | IRNode::UnOp { .. } => false,

        // Calls to .aborts variants return Bool, others may not
        IRNode::Call { function, .. } => !function.variant.returns_bool(),

        // For Blocks, check only the last child
        IRNode::Block { children } => {
            children.last().map_or(false, body_ends_with_non_bool)
        }

        // For If, assume it's valid if either branch could be Bool
        // (this is permissive - better to render than to replace with False)
        IRNode::If { then_branch, else_branch, .. } => {
            body_ends_with_non_bool(then_branch) && body_ends_with_non_bool(else_branch)
        }

        // Let at the end: if the value is an If, the whole thing is probably an abort check pattern
        // Otherwise it's likely a non-Bool binding
        IRNode::Let { value, .. } => {
            !matches!(value.as_ref(), IRNode::If { .. })
        }

        // These standalone at the end are definitely non-Bool
        IRNode::Pack { .. } | IRNode::Field { .. } => true,

        // Var at the end could be a Bool variable from earlier computation
        IRNode::Var(_) => false,

        // WhileAborts returns Bool
        IRNode::WhileAborts { .. } => false,

        // Default: assume it's OK (permissive)
        _ => false,
    }
}

/// Helper to render a function with a given name and optional modified body.
fn render_function_with_name<W: Write>(
    func_id: FunctionID,
    func: &Function,
    name: &str,
    program: &Program,
    current_module_namespace: &str,
    uses_rational: &std::collections::HashSet<FunctionID>,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    // Add 'noncomputable' if function uses Real type
    if uses_rat_type(func, program, uses_rational) {
        w.write("noncomputable ");
    }
    w.write("def ");
    w.write(name);
    render_function_body(func, name, program, current_module_namespace, func_id, uses_rational, w)
}

/// Render a function definition.
pub fn render_function<W: Write>(
    func_id: FunctionID,
    func: &Function,
    program: &Program,
    current_module_namespace: &str,
    w: LeanWriter<W>,
) -> LeanWriter<W> {
    let uses_rational = compute_uses_rational_set(program);
    let escaped_name = escape::escape_identifier(&func.full_name(func_id.variant));
    render_function_with_name(func_id, func, &escaped_name, program, current_module_namespace, &uses_rational, w)
}

/// Render a function as an _impl variant.
/// Used when a spec function provides a clean definition, and the original becomes _impl.
///
/// When the original body contains Abort nodes, we use the Pure variant's body instead,
/// which has aborts stripped out. This ensures the _impl function is always renderable.
pub fn render_function_impl<W: Write>(
    func_id: FunctionID,
    func: &Function,
    program: &Program,
    current_module_namespace: &str,
    w: LeanWriter<W>,
) -> LeanWriter<W> {
    let uses_rational = compute_uses_rational_set(program);
    let base_name = escape::escape_identifier(&func.full_name(func_id.variant));
    let impl_name = format!("{}_impl", base_name);

    // Determine which body to use for rendering:
    // 1. If original_body exists and has aborts, use the Pure variant's body
    // 2. If original_body exists and has no aborts, use original_body
    // 3. Otherwise use the current body
    let func_to_render = if let Some(ref original_body) = func.original_body {
        if original_body.aborts() {
            // Original body has aborts - use Pure variant's body instead
            let pure_id = FunctionID {
                base: func_id.base,
                variant: FunctionVariant::Pure,
            };
            // Try to get the Pure variant; if it doesn't exist, fall back to original
            if let Some(pure_func) = program.functions.try_get(&pure_id) {
                let mut temp_func = func.clone();
                temp_func.body = pure_func.body.clone();
                temp_func
            } else {
                // No Pure variant available, use original (will panic on Abort nodes)
                let mut temp_func = func.clone();
                temp_func.body = original_body.clone();
                temp_func
            }
        } else {
            // Original body has no aborts, use it directly
            let mut temp_func = func.clone();
            temp_func.body = original_body.clone();
            temp_func
        }
    } else {
        func.clone()
    };

    render_function_with_name(func_id, &func_to_render, &impl_name, program, current_module_namespace, &uses_rational, w)
}

/// Render a spec function that targets another function, using the target's name.
/// The spec function replaces the original implementation in the namespace.
pub fn render_spec_with_target_name<W: Write>(
    spec_func_id: FunctionID,
    spec_func: &Function,
    target_name: &str,
    program: &Program,
    current_module_namespace: &str,
    w: LeanWriter<W>,
) -> LeanWriter<W> {
    let uses_rational = compute_uses_rational_set(program);
    let escaped_target_name = escape::escape_identifier(target_name);
    render_function_with_name(spec_func_id, spec_func, &escaped_target_name, program, current_module_namespace, &uses_rational, w)
}

/// Shared function body rendering logic used by both render_function and render_function_impl.
fn render_function_body<W: Write>(
    func: &Function,
    escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    func_id: FunctionID,
    _uses_rational: &std::collections::HashSet<FunctionID>,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {

    // Type parameters with constraints
    render_type_params(&func.signature.type_params, &mut w);

    // Collect used variables in body to detect unused parameters
    let used_vars: BTreeSet<String> = func.body.used_vars().cloned().collect();

    // Parameters - collect Bool params for Decidable constraints
    let mut bool_params = Vec::new();
    for p in &func.signature.parameters {
        let base_name = if p.name.is_empty() || p.name == "_" {
            panic!("BUG: Parameter has empty or underscore name");
        } else {
            escape::escape_identifier(&p.name)
        };
        // Prefix with _ if parameter is not used in body
        let param_name = if used_vars.contains(&p.name) {
            base_name.clone()
        } else {
            format!("_{}", base_name)
        };
        let type_str = type_to_string(&p.param_type, program, Some(current_module_namespace));
        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");

        // Track Bool params - they need Decidable constraints for if-then-else
        // Use param_name which includes the _ prefix when unused
        if matches!(p.param_type, Type::Bool) {
            bool_params.push(param_name.clone());
        }
    }

    // Add Decidable constraints for Bool (Prop) parameters
    for param in &bool_params {
        w.write(" [Decidable ");
        w.write(param);
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

    // Check if this is an aborts function with malformed body (returns non-Bool)
    // This can happen when the aborts transformation produces incorrect IR
    let is_aborts_with_bad_body = func_id.variant == FunctionVariant::Aborts
        && matches!(func.signature.return_type, Type::Bool)
        && body_ends_with_non_bool(&body);

    // Track if body is sorry (can't derive Decidable from sorry)
    let body_is_sorry = body_is_empty && !return_type_is_unit || is_aborts_with_bad_body;

    if body_is_sorry {
        // Malformed aborts function or empty body - for aborts, use False (conservative: says it never aborts)
        // This allows Decidable to be synthesized, which is needed for other code that calls this function
        if func_id.variant == FunctionVariant::Aborts {
            w.write("False");
        } else {
            // Empty function body with non-unit return type is a bug
            // This should never happen in well-formed IR
            panic!(
                "BUG: Function '{}' has empty body but non-unit return type {:?}. \
                This indicates a translation error in the IR generation pipeline.",
                escaped_name, func.signature.return_type
            );
        }
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
    // Skip if body is sorry (non-aborts) - can't derive Decidable from sorry
    // For aborts with bad body, we use False instead of sorry, so Decidable works
    let skip_decidable = body_is_sorry && func_id.variant != FunctionVariant::Aborts;
    let body_is_false = body_is_sorry && func_id.variant == FunctionVariant::Aborts;
    if matches!(func.signature.return_type, Type::Bool) && !skip_decidable {
        w.newline();
        render_decidable_instance(func, &escaped_name, program, current_module_namespace, body_is_false, &mut w);
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
/// If body_is_false is true, the body was replaced with False, so we don't need unfold targets
fn render_decidable_instance<W: Write>(
    func: &Function,
    escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    body_is_false: bool,
    w: &mut LeanWriter<W>,
) {
    // Collect used variables in body to detect unused parameters
    // When body_is_false, no vars are used from original body, so prefix all with _
    let used_vars: BTreeSet<String> = if body_is_false {
        BTreeSet::new()
    } else {
        func.body.used_vars().cloned().collect()
    };

    w.write("instance");

    // Type parameters with constraints
    render_type_params(&func.signature.type_params, w);

    // Collect Bool/Prop parameters that need Decidable constraints
    let mut bool_params = Vec::new();

    // Value parameters - prefix unused ones with _
    for p in &func.signature.parameters {
        let base_name = escape::escape_identifier(&p.name);
        let param_name = if used_vars.contains(&p.name) {
            base_name.clone()
        } else {
            format!("_{}", base_name)
        };
        let type_str = type_to_string(&p.param_type, program, Some(current_module_namespace));
        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");

        // Track Bool params for Decidable constraints - use the actual param name (with _ prefix if unused)
        if matches!(p.param_type, Type::Bool) {
            bool_params.push(param_name.clone());
        }
    }

    // Add Decidable constraints for Bool (Prop) parameters
    for param in &bool_params {
        w.write(" [Decidable ");
        w.write(param);
        w.write("]");
    }

    w.write(" : Decidable (");
    w.write(escaped_name);

    // Type arguments
    for tp in &func.signature.type_params {
        w.write(" ");
        w.write(tp);
    }

    // Value arguments - use the prefixed names consistently
    for p in &func.signature.parameters {
        let base_name = escape::escape_identifier(&p.name);
        let param_name = if used_vars.contains(&p.name) {
            base_name
        } else {
            format!("_{}", base_name)
        };
        w.write(" ");
        w.write(&param_name);
    }

    // Collect all functions that need to be unfolded for Decidable inference
    // This includes any function that returns a type containing Bool/Prop
    // Skip if body was replaced with False - no unfolds needed for False
    let unfold_names = if body_is_false {
        Vec::new()
    } else {
        collect_unfold_targets(&func.body, program, current_module_namespace)
    };

    w.write(") := by unfold ");
    w.write(escaped_name);
    for name in &unfold_names {
        w.write(" ");
        w.write(name);
    }
    w.line("; infer_instance");
}

/// Collect function names that need to be unfolded for Decidable instance derivation.
/// We only need to unfold direct function calls in the body that return Bool/Prop.
/// Recursive unfolding is NOT needed because each called function has its own Decidable instance.
fn collect_unfold_targets(
    body: &IRNode,
    program: &Program,
    current_module_namespace: &str,
) -> Vec<String> {
    use std::collections::HashSet;

    let mut targets = Vec::new();
    let mut visited = HashSet::new();

    // Collect all function calls in the body (immediate calls only, no recursion)
    for func_id in body.calls() {
        if visited.contains(&func_id) {
            continue;
        }
        visited.insert(func_id);

        let func = program.functions.get(&func_id);
        let return_type = &func.signature.return_type;

        // Only unfold if the return type contains Bool (which becomes Prop in Lean)
        if !return_type.contains_bool() {
            continue;
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
    }

    targets
}

/// Render a function with a specific body and name
pub fn render_function_with_body<W: Write>(
    base_id: usize,
    func: &Function,
    body: &IRNode,
    name: &str,
    program: &Program,
    current_module_namespace: &str,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    let uses_rational = compute_uses_rational_set(program);
    let escaped_name = escape::escape_identifier(name);

    // While loops use fuel-based termination (whileLoopFuel), so no 'partial' needed
    if uses_rat_type(func, program, &uses_rational) {
        w.write("noncomputable ");
    }
    w.write("def ");
    w.write(&escaped_name);

    // Create a temporary function with the specified body
    let mut temp_func = func.clone();
    temp_func.body = body.clone();

    render_function_body(&temp_func, &escaped_name, program, current_module_namespace, FunctionID::new(base_id), &uses_rational, w)
}

/// Render a spec-replaced function that takes .requires as a precondition argument
/// For now, this just renders like a normal function - the .requires enforcement
/// happens through the spec_correct theorem which must be proven
pub fn render_spec_replaced_function<W: Write>(
    base_id: usize,
    func: &Function,
    program: &Program,
    current_module_namespace: &str,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    let uses_rational = compute_uses_rational_set(program);
    let escaped_name = escape::escape_identifier(&func.name);

    // While loops use fuel-based termination (whileLoopFuel), so no 'partial' needed
    if uses_rat_type(func, program, &uses_rational) {
        w.write("noncomputable ");
    }
    w.write("def ");
    w.write(&escaped_name);

    // Use render_function_body to render parameters, return type, and body
    render_function_body(func, &escaped_name, program, current_module_namespace, FunctionID::new(base_id), &uses_rational, w)
}
