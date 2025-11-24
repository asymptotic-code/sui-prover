// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Stackless Bytecode to Intermediate Theorem Format Translation
//!
//! This crate translates Move stackless bytecode into the intermediate theorem format (IR).
//! It combines control flow reconstruction with IR translation.
//!
//! Main entry point: `pipeline::translate_program()`
//!
//! Architecture:
//! - pipeline: Orchestrates complete translation
//! - program_builder: Builds program structure (modules, structs, function signatures)
//! - translation/: Specialized translators for different IR levels
//!   - function_translator: Function body translation orchestration
//!   - statement_translator: Bytecode → Statement IR
//!   - expression_translator: Operations → Expression IR
//!   - utilities: Shared conversion utilities
//! - control_flow_reconstruction/: CFG → Structured control flow

pub mod control_flow_reconstruction;
pub mod translation;
mod pipeline;
mod program_builder;
mod package_utils;

pub use control_flow_reconstruction::reconstruct_and_translate;
pub use pipeline::translate_program;
