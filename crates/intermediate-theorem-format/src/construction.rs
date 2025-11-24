// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Construction types for building TheoremProgram
//!
//! These types are used during the construction phase before final IR is created.
//! They contain all necessary data but IDs are created lazily by the builder.

use crate::{FunctionSignature, Statement, TheoremField, VariableRegistry};

/// Construction data for a module
#[derive(Debug, Clone)]
pub struct ModuleConstruction {
    pub name: String,
    pub package_name: String,
}

/// Construction data for a struct
#[derive(Debug, Clone)]
pub struct StructConstruction {
    pub name: String,
    pub qualified_name: String,
    pub type_params: Vec<String>,
    pub fields: Vec<TheoremField>,
}

/// Construction data for a function
#[derive(Debug, Clone)]
pub struct FunctionConstruction {
    pub name: String,
    pub signature: FunctionSignature,
    pub body: Statement,
    pub ssa_registry: VariableRegistry,
    pub is_native: bool,
}
