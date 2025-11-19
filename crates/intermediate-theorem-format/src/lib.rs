// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Intermediate Theorem Format (TheoremIR)
//!
//! This crate provides a language-agnostic intermediate representation between Move's
//! stackless bytecode and verification backends. It does NOT generate backend code -
//! that responsibility belongs to backend crates (move-prover-lean-backend, etc.).

mod data;
pub mod translation;
pub mod analysis;

// Public API exports
pub use analysis::DependencyOrderPass;

// Program and module structures (from data/mod.rs)
pub use data::{TheoremProgram, TheoremModule, NameManager, StructNames, ModuleNames};

// Type aliases for IDs (from data/structure.rs)
pub use data::{TheoremFunctionID, TheoremModuleID, TheoremStructID};

// Struct definitions (from data/structure.rs)
pub use data::structure::{TheoremStruct, TheoremField};

// Function definitions (from data/functions.rs)
pub use data::functions::{TheoremFunction, FunctionSignature, Parameter, LoopVariable};

// Statement definitions (from data/statements.rs)
pub use data::statements::{Statement, PhiVariable};

// Type definitions (from data/types.rs)
pub use data::types::{TheoremType, TempId};

// Expression definitions (from data/expressions.rs)
pub use data::expressions::{Expression, BinOp, UnOp, CallConvention, VectorOp, ConstantValue};

// Variable registry (from data/variables.rs)
pub use data::variables::VariableRegistry;

// Translation pipeline (from translation/mod.rs)
pub use translation::{ProgramBuilder, FunctionTranslator, TranslationPipeline};
