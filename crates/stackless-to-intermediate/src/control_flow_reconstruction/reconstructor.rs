// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Control Flow Reconstruction - Main Orchestration
//!
//! Single-pass approach building Statement IR with expression-based control flow:
//! - If/While are expressions that produce values directly
//! - No separate phi/substitution passes needed
//! - Values flow through expression results

use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::stackless_bytecode::Bytecode;

use super::structure_discovery::discover_structure;
use super::DiscoveryContext;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::Statement;
use intermediate_theorem_format::VariableRegistry;

/// Reconstructs control flow and translates bytecode to Statement IR.
/// Uses expression-based control flow (IfExpr, WhileExpr) - no separate phi computation.
pub fn reconstruct_and_translate<'a, 'b, 'c>(
    builder: &'a mut ProgramBuilder<'b>,
    target: &'a FunctionTarget<'c>,
    code: &'a [Bytecode],
    registry: &'a mut VariableRegistry,
) -> Statement {
    let mut ctx = DiscoveryContext::new(code, builder, target, registry);

    let entry = ctx.forward_cfg.entry_block();
    let exit = ctx.forward_cfg.exit_block();

    // Single-pass: discover structure and build expression-based IR
    discover_structure(&mut ctx, entry, exit)
}
