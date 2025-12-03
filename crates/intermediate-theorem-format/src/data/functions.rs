// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function IR data structures

use crate::analysis;
use crate::data::types::{TempId, TheoremType};
use crate::data::variables::VariableRegistry;
use crate::data::Dependable;
use crate::{IRNode, TheoremModuleID};
use move_model::model::{FunId, QualifiedId};

/// Unique identifier for a function in the program
pub type TheoremFunctionID = usize;

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

    /// Return type
    pub return_type: TheoremType,
}

/// A function represented as structured control flow
#[derive(Debug, Clone)]
pub struct TheoremFunction {
    /// Module this function belongs to
    pub module_id: TheoremModuleID,

    /// Function name (e.g., "empty")
    pub name: String,

    /// Function signature
    pub signature: FunctionSignature,

    /// Function body
    pub body: IRNode,

    /// All of the function's variables
    pub variables: VariableRegistry,

    /// Mutual recursion group ID (None if not mutually recursive)
    /// Functions with the same group ID are mutually recursive and must be defined together
    pub mutual_group_id: Option<usize>,

    /// Whether this function is native (has no bytecode implementation)
    /// Native functions should be provided by backend-specific implementations
    pub is_native: bool,
}

impl TheoremFunction {
    /// Get mutable access to SSA registry
    pub fn variable_registry(&mut self) -> &mut VariableRegistry {
        &mut self.variables
    }

    /// Optimize the function body in place.
    ///
    /// This runs the complete optimization pipeline (see `analysis::optimize`):
    /// The pipeline runs to fix-point automatically.
    pub fn optimize(&mut self) {
        self.body = analysis::optimize(self.body.clone(), &self.variables);
    }
}

impl Dependable for TheoremFunction {
    type Id = TheoremFunctionID;
    type MoveKey = QualifiedId<FunId>;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        self.body.calls().into_iter()
    }

    fn with_mutual_group_id(mut self, group_id: usize) -> Self {
        self.mutual_group_id = Some(group_id);
        self
    }
}
