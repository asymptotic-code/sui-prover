// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translation pipeline orchestrator
//!
//! Coordinates the translation from Move GlobalEnv to TheoremIR Program.
//! Simple sequential pipeline: build structure, translate bodies.

use crate::data::TheoremProgram;
use crate::translation::{ProgramBuilder, FunctionTranslator};
use crate::analysis::DependencyOrderPass;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;

pub struct TranslationPipeline<'env> {
    env: &'env GlobalEnv,
}

impl<'env> TranslationPipeline<'env> {
    pub fn new(env: &'env GlobalEnv) -> Self {
        Self { env }
    }

    /// Run the full translation pipeline
    /// Returns the complete TheoremProgram
    pub fn run(&self, targets: &FunctionTargetsHolder) -> TheoremProgram {
        // Step 1: Build program structure (modules, structs, function signatures)
        // This also populates the NameManager with all struct/module names
        let builder = ProgramBuilder::new(self.env);
        let (mut program, function_id_map, struct_id_map, _module_id_map) = builder.build();

        // Step 2: Translate all function bodies
        // All types are created with resolved struct IDs
        let translator = FunctionTranslator::new(self.env, function_id_map, struct_id_map);
        translator.translate_all(&mut program, targets);

        // Step 3: Topologically sort functions by dependency order
        DependencyOrderPass::run(&mut program);

        program
    }
}
