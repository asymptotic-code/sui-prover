// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control Flow Reconstruction - Main Orchestration
//!
//! Three-phase approach building Statement IR directly:
//! 1. Structure Discovery: Reconstruct CFG into Statement tree (if/else/while)
//! 2. Termination Handling: Identify terminating branches (handled in discovery)
//! 3. Phi-Node Computation: Compute phi-variables using dominance frontiers

use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

use super::loop_substitution::substitute_loop_variables;
use super::structure_discovery::discover_structure;
use super::DiscoveryContext;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::Statement;
use intermediate_theorem_format::VariableRegistry;

/// Reconstructs control flow and translates bytecode to Statement IR directly.
pub fn reconstruct_and_translate<'a, 'b, 'c>(
    builder: &'a mut ProgramBuilder<'b>,
    target: &'a FunctionTarget<'c>,
    code: &'a [Bytecode],
    registry: &'a mut VariableRegistry,
) -> Statement {
    // Discover control flow structure and build Statement IR
    let mut ctx = DiscoveryContext::new(code, builder, target, registry);

    let entry = ctx.forward_cfg.entry_block();
    let exit = ctx.forward_cfg.exit_block();
    let mut result = discover_structure(&mut ctx, entry, exit);

    // Apply SSA renaming for loop variables - replace references to original temps
    // with loop phi_results so that loop bodies reference the current loop state
    result = substitute_loop_variables(result);

    result
}
