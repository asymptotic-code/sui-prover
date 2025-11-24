// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! High-level translation pipeline from Move stackless bytecode to TheoremIR
//!
//! This is the main entry point for backends. Call `translate_program()` to get
//! a complete TheoremProgram with all functions translated and phi-variables computed.

use intermediate_theorem_format::TheoremProgram;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use crate::program_builder::ProgramBuilder;

/// Translate a Move program to TheoremIR
///
/// This is the main entry point for backends. It:
/// 1. Builds the program structure using lazy ID creation
/// 2. Translates all function bodies with CFG reconstruction and phi-variables
/// 3. Validates and converts to TheoremProgram (runs analysis passes internally)
///
/// Returns a complete TheoremProgram ready for backend rendering.
pub fn translate_program(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
) -> TheoremProgram {
    // Build construction data with lazy IDs
    let builder = ProgramBuilder::new(env).build(targets);

    // Convert to final IR (validates all IDs have data, runs analysis passes)
    TheoremProgram::from_builder(builder)
}
