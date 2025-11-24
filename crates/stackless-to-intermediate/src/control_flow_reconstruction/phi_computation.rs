// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Phi-Node Computation Phase
//!
//! Computes phi variables for If statements using dominance frontier analysis.
//! Walks the Statement tree and attaches phi variables to Statement::If nodes.

use intermediate_theorem_format::{Expression, LoopVariable, PhiVariable, Statement, TempId, VariableRegistry};
use std::collections::BTreeMap;

/// Compute phi variables at an if-merge point using data flow analysis
/// Collects all variables assigned in either branch and creates phi nodes
pub fn compute_phi_at_merge(
    then_branch: &Statement,
    else_branch: &Statement,
    registry: &mut VariableRegistry
) -> Vec<PhiVariable> {
    // Check if branches terminate
    let then_terminates = then_branch.terminates();
    let else_terminates = else_branch.terminates();

    // If one branch terminates, no phi variables needed
    // (the terminating branch exits, no values to merge)
    if then_terminates || else_terminates {
        return vec![];
    }

    // Collect all variables assigned in each branch (by name)
    let then_assigns = collect_assignments(then_branch, registry);
    let else_assigns = collect_assignments(else_branch, registry);

    // Union of all assigned variable names
    let mut all_assigned_names: BTreeMap<String, ()> = BTreeMap::new();
    for name in then_assigns.keys() {
        all_assigned_names.insert(name.clone(), ());
    }
    for name in else_assigns.keys() {
        all_assigned_names.insert(name.clone(), ());
    }

    // For each assigned variable, create a phi node
    let mut phi_vars = Vec::new();

    for name in all_assigned_names.keys() {
        let then_temp = then_assigns.get(name);
        let else_temp = else_assigns.get(name);

        // Both branches must assign for a phi (otherwise it's not a merge)
        if let (Some(&then_id), Some(&else_id)) = (then_temp, else_temp) {
            // Get the type from one of the temps
            if let Some(ty) = registry.get_type(then_id) {
                // Allocate phi result
                let phi_result = allocate_fresh_temp(registry);
                registry.set_type(phi_result, ty.clone());
                registry.set_name(phi_result, format!("phi_{}", name));

                phi_vars.push(PhiVariable {
                    result: phi_result,
                    then_value: Expression::Temporary(then_id),
                    else_value: Expression::Temporary(else_id),
                });
            }
        }
    }

    phi_vars
}

/// Collect all assignments in a statement tree (non-recursive shallow traversal)
/// Returns a map from variable name to the last temp ID assigned to that name
/// Only looks at top-level statements in the branch - nested If/While handle their own phis
fn collect_assignments(stmt: &Statement, registry: &VariableRegistry) -> BTreeMap<String, TempId> {
    let mut assigns = BTreeMap::new();
    collect_assignments_shallow(stmt, registry, &mut assigns);
    assigns
}

/// Helper: shallow traversal that doesn't recurse into nested If/While bodies
fn collect_assignments_shallow(
    stmt: &Statement,
    registry: &VariableRegistry,
    assigns: &mut BTreeMap<String, TempId>
) {
    match stmt {
        Statement::Let { results, .. } => {
            for temp in results {
                if let Some(name) = registry.get_name(*temp) {
                    assigns.insert(name.to_string(), *temp);
                }
            }
        }
        Statement::If { phi_vars, .. } => {
            // If has phi vars, those are the merged results - these ARE visible to parent
            for phi in phi_vars {
                if let Some(name) = registry.get_name(phi.result) {
                    let original_name = name.strip_prefix("phi_").unwrap_or(name);
                    assigns.insert(original_name.to_string(), phi.result);
                }
            }
        }
        Statement::While { loop_vars, .. } => {
            // While has loop vars that are the updated results - these ARE visible to parent
            for loop_var in loop_vars {
                if let Some(name) = registry.get_name(loop_var.phi_result) {
                    let original_name = name.strip_prefix("loop_phi_").unwrap_or(name);
                    assigns.insert(original_name.to_string(), loop_var.phi_result);
                }
            }
        }
        Statement::Sequence(stmts) => {
            // Only recurse into sequences - they're not control flow boundaries
            for s in stmts {
                collect_assignments_shallow(s, registry, assigns);
            }
        }
        _ => {}
    }
}

/// Compute loop variables using data flow analysis
/// Finds variables that exist before the loop and are updated in the loop body
pub fn compute_loop_vars(
    body: &Statement,
    registry: &mut VariableRegistry
) -> Vec<LoopVariable> {
    // Collect all assignments in the loop body
    let body_assigns = collect_assignments(body, registry);

    let mut loop_vars = Vec::new();

    for (name, updated_temp) in body_assigns {
        // Find the initial value (the temp with this name before entering the loop)
        // For now, we assume the updated_temp shadows the initial temp
        // In a proper implementation, we'd track the live-in values

        // Skip phi variables from nested ifs/loops
        if name.starts_with("phi_") || name.starts_with("loop_phi_") {
            continue;
        }

        // Get the type from the updated temp
        if let Some(ty) = registry.get_type(updated_temp).cloned() {
            // Allocate phi result for the loop variable
            let phi_result = allocate_fresh_temp(registry);
            registry.set_type(phi_result, ty.clone());
            registry.set_name(phi_result, format!("loop_phi_{}", name));

            loop_vars.push(intermediate_theorem_format::LoopVariable {
                phi_result,
                initial_value: updated_temp, // TODO: Track proper initial value
                updated_value: updated_temp,
                var_type: ty,
            });
        }
    }

    loop_vars
}

/// Allocate a fresh temporary ID
fn allocate_fresh_temp(registry: &VariableRegistry) -> TempId {
    registry.all_temps().into_iter().max().map(|t| t + 1).unwrap_or(1000)
}
