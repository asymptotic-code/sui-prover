// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders TheoremFunction to Lean syntax.

use std::fmt::Write;
use intermediate_theorem_format::{TheoremFunction, TheoremProgram, TheoremType};
use intermediate_theorem_format::analysis::{TempUsageInfo, inline_temps, remove_dead_code, simplify_returns, cleanup, extract_guard_clauses, collect_used_vars, PurityMap};
use super::type_renderer::type_to_string;
use super::statement_renderer::render_stmt;
use super::expression_renderer::RenderCtx;
use super::lean_writer::LeanWriter;
use crate::escape;

/// Render a function definition.
pub fn render_function<W: Write>(func: &TheoremFunction, program: &TheoremProgram, current_module_namespace: &str, purity: &PurityMap, w: &mut LeanWriter<W>) {
    // Check if this function is pure (can't abort)
    let is_pure = purity.get(&func.id).copied().unwrap_or(false);
    let escaped_name = escape::escape_identifier(&func.name);

    // partial def name
    w.write("partial def ");
    w.write(&escaped_name);

    // Type parameters with constraints
    for tp in &func.signature.type_params {
        w.write(&format!(" ({} : Type)", tp));
        w.write(&format!(" [BEq {}]", tp));
        w.write(&format!(" [Inhabited {}]", tp));
    }

    // Parameters
    for p in &func.signature.parameters {
        let param_name = if p.name.is_empty() || p.name == "_" {
            panic!("BUG: Parameter has empty or underscore name");
        } else {
            escape::escape_identifier(&p.name)
        };
        let type_str = type_to_string(&p.param_type, &program.name_manager, Some(current_module_namespace));
        w.write(&format!(" ({} : {})", param_name, type_str));
    }

    // Return type - pure functions don't need Except wrapper
    let return_type = compute_return_type(&func.signature.return_types);
    w.write(" : ");
    if is_pure {
        // Pure function - unwrap Except if present, then render type directly
        let unwrapped = match &return_type {
            TheoremType::Except(inner) => inner.as_ref().clone(),
            other => other.clone(),
        };
        let type_str = type_to_string(&unwrapped, &program.name_manager, Some(current_module_namespace));
        w.write(&type_str);
    } else {
        // Impure function - ensure wrapped in Except
        match &return_type {
            TheoremType::Except(_) => {
                let type_str = type_to_string(&return_type, &program.name_manager, Some(current_module_namespace));
                w.write(&type_str);
            }
            _ => {
                let type_str = type_to_string(&return_type, &program.name_manager, Some(current_module_namespace));
                w.write(&format!("(Except AbortCode {})", type_str));
            }
        }
    }
    w.write(" :=\n");

    // Apply optimizations: inline temps, remove dead code, cleanup, guard clause extraction, simplify returns
    // We run DCE twice - once after inlining, and once after cleanup (which may expose more dead code)
    let usage_info = TempUsageInfo::analyze(&func.body, &func.ssa_registry);
    let inlined = inline_temps(func.body.clone(), &usage_info);
    let without_dead = remove_dead_code(inlined);
    let cleaned = cleanup(without_dead);
    let guarded = extract_guard_clauses(cleaned);
    let simplified = simplify_returns(guarded);
    // Final DCE pass to remove any dead code exposed by previous passes
    let optimized_body = remove_dead_code(simplified);

    // Collect which variable names are actually used in the optimized body
    let used_vars = collect_used_vars(&optimized_body);

    // Function body - pure functions don't need do notation
    if is_pure {
        w.write("  ");
        w.indent();
    } else {
        w.write("  do\n");
        w.indent();
        w.indent();
    }

    let ctx = RenderCtx {
        registry: &func.ssa_registry,
        program,
        current_module_id: func.module_id,
        current_module_namespace: Some(current_module_namespace),
        used_vars: &used_vars,
        purity,
        current_function_pure: is_pure,
    };
    render_stmt(&optimized_body, &ctx, w);

    if is_pure {
        w.dedent();
    } else {
        w.dedent();
        w.dedent();
    }
    w.write("\n");
}

/// Compute return type from signature return types.
fn compute_return_type(return_types: &[TheoremType]) -> TheoremType {
    if return_types.is_empty() {
        TheoremType::Tuple(vec![])
    } else if return_types.len() == 1 {
        return_types[0].clone()
    } else {
        TheoremType::Tuple(return_types.to_vec())
    }
}
