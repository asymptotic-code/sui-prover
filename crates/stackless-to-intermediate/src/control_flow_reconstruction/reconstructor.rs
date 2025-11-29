// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control Flow Reconstruction - Main Orchestration
//!
//! Two-phase approach:
//! 1. Pre-pass: Collect all TraceLocal renames so variables have correct names
//! 2. Main pass: Build Statement IR with expression-based control flow
//!
//! The pre-pass is necessary because TraceLocal instructions come AFTER the
//! assignment instructions in bytecode, but we need the renamed names when
//! creating the Let statement patterns.

use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};

use super::structure_discovery::discover_structure;
use super::DiscoveryContext;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::{Statement, TempId};
use intermediate_theorem_format::VariableRegistry;

/// Pre-pass: Collect all TraceLocal renames and apply them before translation.
/// This ensures that when we create Let statements, the variable names are already correct.
fn apply_trace_local_renames(code: &[Bytecode], registry: &mut VariableRegistry) {
    for bytecode in code {
        if let Bytecode::Call(_, _, Operation::TraceLocal(local_idx), srcs, _) = bytecode {
            if !srcs.is_empty() {
                let temp_id = srcs[0] as TempId;
                let local_id = *local_idx as TempId;

                // Get the name of the user variable at local_idx
                if let Some(local_name) = registry.get_name(local_id) {
                    // Only rename if local has a meaningful name (not a generic temp)
                    let is_generic = is_generic_temp_name(local_name);
                    if !is_generic {
                        registry.rename_bytecode_temp_if_generic(temp_id, local_name.to_string());
                    }
                }
            }
        }
    }
}

/// Check if a name is a generic temp name like "t0", "t123", "tmp__1"
fn is_generic_temp_name(name: &str) -> bool {
    // Pattern: t followed by only digits
    if name.starts_with('t') && name.len() > 1 && name[1..].chars().all(|c| c.is_ascii_digit()) {
        return true;
    }
    // Pattern: tmp__ followed by anything
    if name.starts_with("tmp__") {
        return true;
    }
    false
}

/// Reconstructs control flow and translates bytecode to Statement IR.
/// Uses expression-based control flow (IfExpr, WhileExpr) - no separate phi computation.
pub fn reconstruct_and_translate<'a, 'b, 'c>(
    builder: &'a mut ProgramBuilder<'b>,
    target: &'a FunctionTarget<'c>,
    code: &'a [Bytecode],
    registry: &'a mut VariableRegistry,
) -> Statement {
    // Pre-pass: Apply TraceLocal renames so all temps have their final names
    // before we start creating statements.
    apply_trace_local_renames(code, registry);

    let mut ctx = DiscoveryContext::new(code, builder, target, registry);

    let entry = ctx.forward_cfg.entry_block();
    let exit = ctx.forward_cfg.exit_block();

    // Main pass: discover structure and build expression-based IR
    discover_structure(&mut ctx, entry, exit)
}
