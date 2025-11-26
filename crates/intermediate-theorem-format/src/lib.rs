// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Intermediate Theorem Format (TheoremIR)
//!
//! This crate provides a language-agnostic intermediate representation between Move's
//! stackless bytecode and verification backends. It does NOT generate backend code -
//! that responsibility belongs to backend crates (move-prover-lean-backend, etc.).

mod data;
pub mod analysis;
mod construction;
mod lazy_builder;

// Public API exports
pub use analysis::DependencyOrderPass;

// Program and module structures (from data/mod.rs)
pub use data::{TheoremProgram, TheoremModule, NameManager, StructNames, ModuleNames};

// Type aliases for IDs (from data/structure.rs)
pub use data::{TheoremFunctionID, TheoremModuleID, TheoremStructID};

// Struct definitions (from data/structure.rs)
pub use data::structure::{TheoremStruct, TheoremField};

// Function definitions (from data/functions.rs)
pub use data::functions::{TheoremFunction, FunctionSignature, Parameter};

// Statement definitions (from data/statements.rs)
pub use data::statements::{Statement, StatementIter, ExpressionIter};

// Type definitions (from data/types.rs)
pub use data::types::{TheoremType, TempId};

// Expression definitions (from data/expressions.rs)
pub use data::expressions::{Expression, BinOp, UnOp, CallConvention, VectorOp, ConstantValue, Block, LoopState};

// Variable registry (from data/variables.rs)
pub use data::variables::{VariableRegistry, TempKind, TempData};

// Construction types (for building IR)
pub use construction::{FunctionConstruction, ModuleConstruction, StructConstruction};

// Lazy builder (for ID allocation during construction)
pub use lazy_builder::LazyIdBuilder;
