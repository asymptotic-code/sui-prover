// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function IR data structures

use crate::data::variables::VariableRegistry;
use crate::data::types::{TempId, TheoremType};
use crate::data::statements::Statement;
use crate::TheoremModuleID;
use crate::data::Dependable;

/// Unique identifier for a function in the program
pub type TheoremFunctionID = usize;

/// Represents a loop-carried variable with SSA phi-node values.
#[derive(Debug, Clone)]
pub struct LoopVariable {
    /// The SSA value representing this variable within the loop (phi node result)
    pub phi_result: TempId,
    /// The SSA value before entering the loop (phi node input from outside)
    pub initial_value: TempId,
    /// The SSA value produced by the loop body (phi node input from loop)
    pub updated_value: TempId,
    /// The type of this variable
    pub var_type: TheoremType,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Parameter {
    /// Parameter name
    pub name: String,

    /// Parameter type
    pub param_type: TheoremType,

    /// SSA value for this parameter
    pub ssa_value: TempId,
}

/// Function signature
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    /// Type parameters
    pub type_params: Vec<String>,

    /// Parameters
    pub parameters: Vec<Parameter>,

    /// Return types
    pub return_types: Vec<TheoremType>,
}

/// A function represented as structured control flow
#[derive(Debug, Clone)]
pub struct TheoremFunction {
    /// TheoremIR function identifier (index in TheoremProgram.functions)
    pub id: TheoremFunctionID,

    /// TheoremIR module identifier (which module owns this function)
    pub module_id: TheoremModuleID,

    /// Function name (e.g., "empty")
    pub name: String,

    /// Function signature
    pub signature: FunctionSignature,

    /// Function body as a structured statement
    pub body: Statement,

    /// SSA registry - single source of truth for all temporaries
    pub ssa_registry: VariableRegistry,

    /// Mutual recursion group ID (None if not mutually recursive)
    /// Functions with the same group ID are mutually recursive and must be defined together
    pub mutual_group_id: Option<usize>,

    /// Whether this function is native (has no bytecode implementation)
    /// Native functions should be provided by backend-specific implementations
    pub is_native: bool,
}

impl TheoremFunction {
    /// Get mutable access to SSA registry
    pub fn ssa_registry_mut(&mut self) -> &mut VariableRegistry {
        &mut self.ssa_registry
    }
}

impl Dependable for TheoremFunction {
    type Id = TheoremFunctionID;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        self.body.calls()
    }

    fn with_mutual_group_id(mut self, group_id: usize) -> Self {
        self.mutual_group_id = Some(group_id);
        self
    }
}
