// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use intermediate_theorem_format::{
    Const, Function, FunctionID, FunctionVariant, IRNode, Program, Type,
};
use std::collections::BTreeSet;
use std::fmt::Write;

use super::context::RenderCtx;
use super::lean_writer::LeanWriter;
use super::render;
use super::type_renderer::type_to_string_with_params;
use crate::escape;

/// Check if a function uses the Real type (which is noncomputable in Lean).
/// This checks signature types AND transitive calls to Real-using functions.
fn uses_rat_type(
    func: &Function,
    program: &Program,
    uses_rational: &std::collections::HashSet<FunctionID>,
) -> bool {
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

/// Check if a function's signature uses Real types (stricter check, ignores body).
/// Used for _impl functions which only have integer/bitwise operations.
fn signature_uses_real(func: &Function, program: &Program) -> bool {
    // Check parameters
    for p in &func.signature.parameters {
        if type_contains_rat(&p.param_type, program) {
            return true;
        }
    }
    // Check return type
    type_contains_rat(&func.signature.return_type, program)
}

/// Recursively check if a type contains Real.
fn type_contains_rat(ty: &Type, program: &Program) -> bool {
    match ty {
        Type::Struct {
            struct_id,
            type_args,
        } => {
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

/// Compute the set of all functions that transitively use real module.
/// This is done once at the start to avoid infinite recursion and redundant computation.
///
/// IMPORTANT: Only Runtime variant functions are considered for noncomputable propagation.
/// Spec functions (Requires, Ensures, etc.) may use Real types for specification purposes,
/// but this doesn't make the implementation noncomputable. Only actual runtime calls to
/// real module functions make a function noncomputable.
///
/// Additionally, when a function has original_body set (meaning it has a spec replacement),
/// calls to that function from other impl code will be rendered as calls to _impl.
/// In that case, we check if the original_body uses Real, not the spec body.
fn compute_uses_rational_set(program: &Program) -> std::collections::HashSet<FunctionID> {
    let mut uses_rational = std::collections::HashSet::new();

    // First pass: identify direct users (real module functions only)
    // Note: native functions are NOT automatically noncomputable - they are implemented in Lean
    // and are computable unless they specifically use Real types.
    for (func_id, func) in program.functions.iter() {
        let module = program.modules.get(func.module_id);
        if module.name == "real" {
            uses_rational.insert(func_id);
        }
    }

    // Fixed-point iteration: propagate to callers
    // Only propagate through Runtime variant calls - spec functions using Real
    // don't make implementations noncomputable.
    let mut changed = true;
    while changed {
        changed = false;
        for (func_id, func) in program.functions.iter() {
            if uses_rational.contains(&func_id) {
                continue; // Already marked
            }

            // Check the function's body for calls
            let body_to_check = &func.body;

            // Check if this function calls any marked function via Runtime variant
            // Spec variant calls (Requires, Ensures, etc.) don't count - they're for verification only
            let calls_marked = body_to_check.calls().any(|call_id| {
                if !call_id.is_runtime() {
                    return false;
                }
                uses_rational.contains(&call_id)
            });

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
/// Only considers Runtime variant calls - spec variant calls don't affect computability.
fn body_calls_rational_module_transitive(
    body: &IRNode,
    uses_rational: &std::collections::HashSet<FunctionID>,
) -> bool {
    body.calls()
        .any(|func_id| func_id.is_runtime() && uses_rational.contains(&func_id))
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
        IRNode::Block { children } => children.last().is_some_and(body_ends_with_non_bool),

        // For If, assume it's valid if either branch could be Bool
        // (this is permissive - better to render than to replace with False)
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => body_ends_with_non_bool(then_branch) && body_ends_with_non_bool(else_branch),

        // Let at the end: if the value is an If, the whole thing is probably an abort check pattern
        // Otherwise it's likely a non-Bool binding
        IRNode::Let { value, .. } => !matches!(value.as_ref(), IRNode::If { .. }),

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

/// Check if a body produces an Except value (i.e., the result type is Except).
/// This checks if the terminal expression calls a function that returns Except.
///
/// IMPORTANT: Implementation functions (those without spec_target and with Runtime variant)
/// have their Except wrapper STRIPPED when rendered to Lean. They return the inner type
/// directly, with aborts conditions rendered separately.
/// So we need to check if the call will actually produce Except in the rendered code.
fn body_produces_except_value(body: &IRNode, program: &Program) -> bool {
    match body {
        // Block: check the last child (the result)
        IRNode::Block { children } => children
            .last()
            .is_some_and(|c| body_produces_except_value(c, program)),

        // Call: check if the called function returns Except
        IRNode::Call { function, .. } => {
            let func = program.functions.get(function);

            // Implementation functions (no spec_target, Runtime variant) have Except stripped
            // when rendered - they return the inner type directly
            let is_impl_function =
                func.spec_target.is_none() && function.variant == FunctionVariant::Runtime;

            // If it's an impl function, the rendered code doesn't return Except,
            // even if the IR signature says Except
            if is_impl_function {
                false // Impl functions have Except stripped when rendered
            } else {
                func.signature.return_type.is_monad()
            }
        }

        // Let: check what the body evaluates to (if it's the last expr, it's the let value)
        // But if there's more after the let, it depends on what follows
        IRNode::Let { value, .. } => body_produces_except_value(value, program),

        // If: both branches must produce Except for the whole thing to produce Except
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => {
            body_produces_except_value(then_branch, program)
                && body_produces_except_value(else_branch, program)
        }

        // Return: check the returned value(s)
        IRNode::Return(values) => values
            .first()
            .is_some_and(|v| body_produces_except_value(v, program)),

        // Other expressions (Var, Const, Pack, Field, etc.) don't produce Except
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
    // Only mark as noncomputable if the function uses Real types (which are genuinely noncomputable).
    // Otherwise, keep it computable to enable native_decide for proofs.
    let needs_noncomputable = uses_rat_type(func, program, uses_rational);
    if needs_noncomputable {
        w.write("noncomputable def ");
    } else {
        w.write("def ");
    }
    w.write(name);
    render_function_body(
        func,
        name,
        program,
        current_module_namespace,
        func_id,
        uses_rational,
        w,
    )
}

/// Detect sequential Let chains that rebind the same variable (step pattern).
/// Returns a list of (new_step_number, original_block_index, condition, value) tuples if the pattern is detected.
/// new_step_number starts from 1 and increments sequentially.
/// original_block_index is the index in the original Block children for prerequisite rendering.
fn detect_step_pattern(body: &IRNode) -> Option<Vec<(usize, usize, Option<IRNode>, IRNode)>> {
    // We're looking for a pattern like:
    // let x = initial_value
    // let x = if cond1 then update1 else x
    // let x = if cond2 then update2 else x
    // ...
    // x (or some final expression using x)

    let children = match body {
        IRNode::Block { children } => children,
        _ => return None,
    };

    if children.len() < 3 {
        return None; // Need at least initial let + 1 update + result
    }

    // Find the variable that gets repeatedly rebound with conditionals
    // Look for the first Let followed by another Let with the same var and an If pattern
    let mut found_pattern_start = None;
    for i in 0..children.len() - 1 {
        if let IRNode::Let {
            pattern: p1,
            value: v1,
        } = &children[i]
        {
            if p1.len() == 1 {
                if let IRNode::Let {
                    pattern: p2,
                    value: v2,
                } = &children[i + 1]
                {
                    if p2.len() == 1 && p2[0] == p1[0] {
                        // Check if v2 is an If with else branch being the same var
                        if let IRNode::If { else_branch, .. } = v2.as_ref() {
                            if matches!(else_branch.as_ref(), IRNode::Var(v) if v == &p1[0]) {
                                found_pattern_start = Some((i, p1[0].clone(), v1.as_ref().clone()));
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    let (start_idx, var_name, initial_value) = found_pattern_start?;

    let mut steps = vec![(start_idx, None, initial_value)];

    // Check subsequent children for the pattern: let var = if cond then update else var
    for (idx, child) in children.iter().enumerate().skip(start_idx + 1) {
        match child {
            IRNode::Let { pattern, value } if pattern.len() == 1 && pattern[0] == var_name => {
                // Check if value is an If that reassigns or keeps the same variable
                match value.as_ref() {
                    IRNode::If {
                        cond,
                        then_branch,
                        else_branch,
                    } => {
                        // Check if else_branch is just the variable (identity case)
                        let is_identity_else =
                            matches!(else_branch.as_ref(), IRNode::Var(v) if v == &var_name);

                        if is_identity_else {
                            // This is a conditional update step
                            steps.push((
                                idx,
                                Some(cond.as_ref().clone()),
                                then_branch.as_ref().clone(),
                            ));
                        } else {
                            // Not the expected pattern
                            return None;
                        }
                    }
                    _ => {
                        // Not an If, might be final transformation
                        // Check if this is the last Let before a return/var
                        if idx == children.len() - 2 {
                            steps.push((idx, None, value.as_ref().clone()));
                        } else {
                            return None;
                        }
                    }
                }
            }
            IRNode::Var(v) if v == &var_name && idx == children.len() - 1 => {
                // Final result is just the variable - OK, this completes the pattern
                break;
            }
            _ => {
                // Non-matching node in the chain
                if idx == children.len() - 1 {
                    // Last node might be a complex expression, accept it
                    break;
                }
                return None;
            }
        }
    }

    // Need at least 2 steps to be worth generating
    if steps.len() >= 2 {
        // Renumber steps sequentially starting from 1
        // This ensures we get step_1, step_2, step_3... instead of gaps in numbering
        let renumbered_steps: Vec<_> = steps
            .into_iter()
            .enumerate()
            .map(|(new_idx, (old_idx, cond, val))| (new_idx + 1, old_idx, cond, val))
            .collect();
        Some(renumbered_steps)
    } else {
        None
    }
}

/// Render step definitions for a function with sequential Let chains.
/// Returns true if steps were rendered, false otherwise.
///
/// NOTE: Step generation is DISABLED. The step functions were intended as an optimization
/// to break down complex conditional chains, but they actually make proofs harder because:
/// 1. Each step repeats all prerequisite computations, creating redundancy
/// 2. The step functions are not compositional - proofs can't reason about individual steps
/// 3. The generated code doesn't match the proof structure expected by UserProofs
///
/// Instead, we now render the function body directly as a single definition.
fn render_step_definitions<W: Write>(
    _func: &Function,
    _escaped_name: &str,
    _program: &Program,
    _current_module_namespace: &str,
    w: LeanWriter<W>,
) -> (LeanWriter<W>, bool) {
    // Step generation disabled - always return false to skip step rendering
    //
    // The step functions were intended as an optimization to break down complex
    // conditional chains, but they actually make proofs harder because:
    // 1. Each step repeats all prerequisite computations, creating redundancy
    // 2. The step functions are not compositional - proofs can't reason about individual steps
    // 3. The generated code doesn't match the proof structure expected by UserProofs
    //
    // The original implementation has been removed. If step generation is needed in the future,
    // it should be redesigned to produce compositional definitions that proofs can use.
    (w, false)
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

    // Try to render step definitions first
    let (w, has_steps) =
        render_step_definitions(func, &escaped_name, program, current_module_namespace, w);

    // Always render the main function (steps are supplementary)
    render_function_with_name(
        func_id,
        func,
        &escaped_name,
        program,
        current_module_namespace,
        &uses_rational,
        w,
    )
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

    // With the new architecture, impl and spec are separate - just render the function as-is
    let func_to_render = func.clone();

    // Try to render step definitions for _impl functions
    let (w, _has_steps) = render_step_definitions(
        &func_to_render,
        &impl_name,
        program,
        current_module_namespace,
        w,
    );

    render_function_with_name(
        func_id,
        &func_to_render,
        &impl_name,
        program,
        current_module_namespace,
        &uses_rational,
        w,
    )
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
    render_function_with_name(
        spec_func_id,
        spec_func,
        &escaped_target_name,
        program,
        current_module_namespace,
        &uses_rational,
        w,
    )
}

/// Shared function body rendering logic used by both render_function and render_function_impl.
fn render_function_body_with_generics<W: Write>(
    func: &Function,
    escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    func_id: FunctionID,
    uses_rational: &std::collections::HashSet<FunctionID>,
    generic_spec: Option<&intermediate_theorem_format::analysis::GenericSpec>,
    w: LeanWriter<W>,
) -> LeanWriter<W> {
    // Use generic rendering if we have generic spec metadata
    if let Some(spec) = generic_spec {
        render_function_body_generic(
            func,
            escaped_name,
            program,
            current_module_namespace,
            func_id,
            uses_rational,
            spec,
            w,
        )
    } else {
        render_function_body(
            func,
            escaped_name,
            program,
            current_module_namespace,
            func_id,
            uses_rational,
            w,
        )
    }
}

fn render_function_body<W: Write>(
    func: &Function,
    escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    func_id: FunctionID,
    uses_rational: &std::collections::HashSet<FunctionID>,
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
        let type_str = type_to_string_with_params(
            &p.param_type,
            program,
            Some(current_module_namespace),
            Some(&func.signature.type_params),
        );
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
        let type_str = type_to_string_with_params(
            &func.signature.return_type,
            program,
            Some(current_module_namespace),
            Some(&func.signature.type_params),
        );
        w.write(&type_str);
    }
    w.line(" :=");

    // Function body (strip requires/ensures nodes - they go in Specs/)
    w.indent(false);

    // Body is already optimized by Program::finalize() in the IR layer
    let body = &func.body;

    // Check if body is empty block and return type is not unit - use sorry
    let body_is_empty = matches!(&body, IRNode::Block { children } if children.is_empty());
    let return_type_is_unit = matches!(&func.signature.return_type, Type::Tuple(v) if v.is_empty())
        || (func.signature.return_type.is_monad()
            && matches!(func.signature.return_type.unwrap_monad(), Some(Type::Tuple(v)) if v.is_empty()));

    // Check if this is an aborts function with malformed body (returns non-Bool)
    // This can happen when the aborts transformation produces incorrect IR
    let is_aborts_with_bad_body = func_id.variant == FunctionVariant::Aborts
        && matches!(func.signature.return_type, Type::Bool)
        && body_ends_with_non_bool(body);

    // Track if body is sorry (can't derive Decidable from sorry)
    let body_is_sorry = body_is_empty && !return_type_is_unit || is_aborts_with_bad_body;

    if body_is_sorry {
        // Malformed aborts function or empty body - for aborts, use False (conservative: says it never aborts)
        // This allows Decidable to be synthesized, which is needed for other code that calls this function
        if func_id.variant == FunctionVariant::Aborts {
            w.write("False");
        } else {
            // Empty function body with non-unit return type - use sorry
            // This can happen for native functions or functions with empty bytecode
            w.write("sorry");
        }
    } else if body_is_empty && return_type_is_unit {
        // Empty body returning unit - render ()
        w.write("()");
    } else {
        // Check if the return type can abort but the body produces a pure value
        // In this case, we need to wrap the body with `pure`
        let return_type_can_abort = func.signature.return_type.is_monad();
        // A body produces Except if it calls a function that returns Except
        // Just checking can_abort() isn't enough - we need to check if the called
        // functions actually return Except types
        let body_produces_except = body_produces_except_value(body, program);
        let needs_pure_wrapper = return_type_can_abort && !body_produces_except;

        // Note: Even spec functions use Bool operations in their body.
        // The Bool result is coerced to Prop by Lean's type system.
        let mut ctx = RenderCtx::new(
            program,
            &func.variables,
            func.module_id,
            Some(current_module_namespace),
            w,
        );

        // For .aborts functions, Bool should render as Prop
        if func_id.variant == FunctionVariant::Aborts {
            ctx.with_bool_as_prop();
        }

        if needs_pure_wrapper {
            ctx.write("pure (");
        }

        // Wrap non-Block bodies in a Block so Block handles do-notation uniformly
        let body_to_render = match &body {
            IRNode::Block { .. } => body.clone(),
            _ => IRNode::Block {
                children: vec![body.clone()],
            },
        };

        render::render(&body_to_render, &mut ctx);

        if needs_pure_wrapper {
            ctx.write(")");
        }

        w = ctx.into_writer();
    }

    w.dedent(false);
    w.newline();

    w
}

/// Render type parameters with constraints.
/// For "U" (generic real operations), use `[HasRealOps U]`
/// For others, use `[BEq T] [Inhabited T]`
fn render_type_params<W: Write>(type_params: &[String], w: &mut LeanWriter<W>) {
    for tp in type_params {
        w.write(" (");
        w.write(tp);
        w.write(" : Type)");

        // Use HasRealOps for "U" (generic real operations parameter)
        if tp == "U" {
            w.write(" [HasRealOps ");
            w.write(tp);
            w.write("]");
        } else {
            // Standard constraints for other type parameters
            w.write(" [BEq ");
            w.write(tp);
            w.write("] [Inhabited ");
            w.write(tp);
            w.write("]");
        }
    }
}

/// Render type parameters with inferred typeclass constraints from GenericSpec
fn render_generic_type_params<W: Write>(
    generic_spec: &intermediate_theorem_format::analysis::GenericSpec,
    w: &mut LeanWriter<W>,
) {
    // Render each type parameter with its constraints
    for type_param in generic_spec.type_params.keys() {
        w.write(" (");
        w.write(type_param);
        w.write(" : Type)");

        // Add inferred typeclass constraints
        if let Some(constraints) = generic_spec.constraints.get(type_param) {
            for constraint in constraints {
                w.write(" [");
                w.write(constraint.lean_name());
                w.write(" ");
                w.write(type_param);
                w.write("]");
            }
        }
    }
}

/// Render a generic spec function with typeclass constraints
fn render_function_body_generic<W: Write>(
    func: &Function,
    _escaped_name: &str,
    program: &Program,
    current_module_namespace: &str,
    func_id: FunctionID,
    _uses_rational: &std::collections::HashSet<FunctionID>,
    generic_spec: &intermediate_theorem_format::analysis::GenericSpec,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    // Type parameters with inferred typeclass constraints
    render_generic_type_params(generic_spec, &mut w);

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

        // Use generic type parameter if this parameter was genericized
        let type_str = if let Some(type_param) = generic_spec.type_substitutions.get(&p.name) {
            type_param.clone()
        } else {
            type_to_string_with_params(
                &p.param_type,
                program,
                Some(current_module_namespace),
                Some(&func.signature.type_params),
            )
        };

        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");

        // Track Bool params - they need Decidable constraints for if-then-else
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

    // Return type - check if it was genericized
    w.write(" : ");
    if func_id.variant.returns_bool() && matches!(func.signature.return_type, Type::Bool) {
        w.write("Prop");
    } else {
        // Check if return type should be generic based on the type params we inferred
        let return_type_str = if generic_spec.type_params.contains_key("U")
            && matches!(func.signature.return_type, Type::UInt(_))
        {
            "U".to_string()
        } else if generic_spec.type_params.contains_key("I")
            && matches!(func.signature.return_type, Type::SInt(_))
        {
            "I".to_string()
        } else {
            type_to_string_with_params(
                &func.signature.return_type,
                program,
                Some(current_module_namespace),
                Some(&func.signature.type_params),
            )
        };
        w.write(&return_type_str);
    }

    w.write(" :=");
    w.newline();
    w.indent(false);

    // Render function body with generic spec context for MoveReal transformation
    let mut ctx = RenderCtx::new(
        program,
        &func.variables,
        func.module_id,
        Some(current_module_namespace),
        w,
    );

    // Set generic spec metadata so the renderer can transform MoveReal calls
    ctx.with_generic_spec(generic_spec);

    // Wrap non-Block bodies in a Block
    let body_to_render = match &func.body {
        IRNode::Block { .. } => func.body.clone(),
        _ => IRNode::Block {
            children: vec![func.body.clone()],
        },
    };

    render::render(&body_to_render, &mut ctx);

    let mut w = ctx.into_writer();
    w.dedent(false);
    w.newline();
    w
}

/// Render a function with a specific body and name
/// For _impl functions (name ends with "_impl"), uses stricter noncomputable check
/// since the body is the original implementation (integer/bitwise only).
pub fn render_function_with_body<W: Write>(
    base_id: usize,
    func: &Function,
    body: &IRNode,
    name: &str,
    program: &Program,
    current_module_namespace: &str,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    let escaped_name = escape::escape_identifier(name);

    // For _impl functions, only mark noncomputable if signature uses Real
    // (the body is pure integer/bitwise operations from the original impl)
    // For spec functions, check full transitive Real usage
    let is_impl_function = name.ends_with("_impl");
    let needs_noncomputable = if is_impl_function {
        signature_uses_real(func, program)
    } else {
        let uses_rational = compute_uses_rational_set(program);
        uses_rat_type(func, program, &uses_rational)
    };

    // Create a temporary function with the specified body for step detection
    let mut temp_func = func.clone();
    temp_func.body = body.clone();

    // Try to render step definitions for _impl functions
    if is_impl_function {
        let (new_w, _has_steps) = render_step_definitions(
            &temp_func,
            &escaped_name,
            program,
            current_module_namespace,
            w,
        );
        w = new_w;
    }

    if needs_noncomputable {
        w.write("noncomputable def ");
    } else {
        w.write("def ");
    }
    w.write(&escaped_name);

    // uses_rational is not used by render_function_body, pass empty
    let empty_uses_rational = std::collections::HashSet::new();
    render_function_body(
        &temp_func,
        &escaped_name,
        program,
        current_module_namespace,
        FunctionID::new(base_id),
        &empty_uses_rational,
        w,
    )
}

/// Render an axiom stub for a native function that is a spec target.
/// This is used for functions that couldn't be translated (e.g., those with while loops)
/// but are still referenced by specs. The stub declares the function as an axiom
/// so the goal can reference it.
///
/// Also generates a correctness axiom that relates the impl to its mathematical specification,
/// which can be used in proofs to bridge the gap between the opaque impl and the spec.
pub fn render_axiom_stub<W: Write>(
    _base_id: usize,
    func: &Function,
    name: &str,
    program: &Program,
    current_module_namespace: &str,
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    use super::type_renderer::type_to_string_with_params;

    let escaped_name = escape::escape_identifier(name);
    let base_func_name = name.trim_end_matches("_impl");

    w.write("-- Axiom stub for native spec target (e.g., function with while loops)\n");
    w.write("axiom ");
    w.write(&escaped_name);

    // Type parameters
    for tp in &func.signature.type_params {
        w.write(" (");
        w.write(tp);
        w.write(" : Type)");
        w.write(" [BEq ");
        w.write(tp);
        w.write("] [Inhabited ");
        w.write(tp);
        w.write("]");
    }

    // Parameters
    for p in &func.signature.parameters {
        let param_name = escape::escape_identifier(&p.name);
        let type_str = type_to_string_with_params(
            &p.param_type,
            program,
            Some(current_module_namespace),
            Some(&func.signature.type_params),
        );
        w.write(" (");
        w.write(&param_name);
        w.write(" : ");
        w.write(&type_str);
        w.write(")");
    }

    // Return type
    w.write(" : ");
    let return_type_str = type_to_string_with_params(
        &func.signature.return_type,
        program,
        Some(current_module_namespace),
        Some(&func.signature.type_params),
    );
    w.write(&return_type_str);
    w.newline();
    w.newline();

    // Generate a correctness axiom for specific known native functions
    // These axioms express what the native implementation computes mathematically
    if base_func_name == "mul_div_floor" {
        w.write("-- Axiom stating correctness of the native implementation\n");
        w.write("-- This function computes floor((num1 * num2) / denom) which equals the Nat division\n");
        w.write("-- The native implementation is assumed to match this behavior exactly\n");
        w.write("axiom ");
        w.write(&escaped_name);
        w.write("_correct (num1 : BoundedNat (2^128)) (num2 : BoundedNat (2^128)) (denom : BoundedNat (2^128)) (h : denom.val > 0) :\n");
        w.write("  ");
        w.write(&escaped_name);
        w.write(" num1 num2 denom = ⟨(num1.val * num2.val) / denom.val % (2^128), by omega⟩\n");
        w.newline();
    }

    w
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

    let func_id = FunctionID::new(base_id);

    // IMPORTANT: Do NOT use generic_spec metadata here!
    // This function renders the spec body for a spec-TARGET function.
    // The target function has concrete types in its signature, and we want to preserve those.
    // Generic metadata is for rendering standalone spec functions, not replacements.

    // While loops use fuel-based termination (whileLoopFuel), so no 'partial' needed
    // Only mark as noncomputable if the function uses Real types
    let needs_noncomputable = uses_rat_type(func, program, &uses_rational);
    if needs_noncomputable {
        w.write("noncomputable def ");
    } else {
        w.write("def ");
    }
    w.write(&escaped_name);

    // Use render_function_body WITHOUT generic metadata - use the concrete target signature
    render_function_body_with_generics(
        func,
        &escaped_name,
        program,
        current_module_namespace,
        func_id,
        &uses_rational,
        None, // No generics - use concrete types from the target function
        w,
    )
}
