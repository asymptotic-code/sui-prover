// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translation from Move bytecode to TheoremIR
//!
//! Clean, modular translation with single responsibilities:
//! - program_builder: Builds TheoremProgram from GlobalEnv
//! - function_translator: Translates function bytecode to Statement IR
//! - bytecode_translator: Centralized bytecode to statement translation (1:1 mapping)

pub mod program_builder;
pub mod function_translator;
pub mod bytecode_translator;
pub mod pipeline;

// Deprecated - being replaced by bytecode_translator
pub mod statement_translator;
pub mod expression_translator;

pub use program_builder::ProgramBuilder;
pub use function_translator::FunctionTranslator;
pub use bytecode_translator::BytecodeTranslator;
pub use pipeline::TranslationPipeline;
