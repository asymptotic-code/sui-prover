// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function IR data structures

use crate::analysis;
use crate::data::types::{TempId, Type};
use crate::data::variables::{TypeContext, VariableRegistry};
use crate::data::Dependable;
use crate::{IRNode, ModuleID};
use move_model::model::{FunId, QualifiedId};

/// Function variant - distinguishes between the original function and derived versions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub enum FunctionVariant {
    /// The original runtime function
    #[default]
    Runtime,
    /// Pure version (non-monadic, assumes no abort)
    Pure,
    /// Aborts predicate (returns Bool indicating if function aborts)
    Aborts,
    /// Requires predicate (precondition)
    Requires,
    /// Ensures predicate (postcondition), with index for multiple ensures
    Ensures(usize),
}

impl FunctionVariant {
    /// Get the suffix string for this variant
    pub fn suffix(&self) -> &'static str {
        match self {
            FunctionVariant::Runtime => "",
            FunctionVariant::Pure => ".pure",
            FunctionVariant::Aborts => ".aborts",
            FunctionVariant::Requires => ".requires",
            FunctionVariant::Ensures(_) => ".ensures",
        }
    }

    /// Check if this is a spec-derived variant
    pub fn is_spec_variant(&self) -> bool {
        matches!(self, FunctionVariant::Requires | FunctionVariant::Ensures(_))
    }

    /// Check if this variant returns Bool (Prop)
    pub fn returns_bool(&self) -> bool {
        !matches!(self, FunctionVariant::Runtime | FunctionVariant::Pure)
    }
}

/// Unique identifier for a function in the program.
/// Combines a base ID (index into function storage) with a variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionID {
    /// The base function index
    pub base: usize,
    /// The function variant
    pub variant: FunctionVariant,
}

impl FunctionID {
    /// Create a new FunctionID for a runtime function
    pub fn new(base: usize) -> Self {
        Self {
            base,
            variant: FunctionVariant::Runtime,
        }
    }

    /// Create a FunctionID with a specific variant
    pub fn with_variant(base: usize, variant: FunctionVariant) -> Self {
        Self { base, variant }
    }

    /// Get the same function but with a different variant
    pub fn to_variant(self, variant: FunctionVariant) -> Self {
        Self { variant, ..self }
    }

    /// Check if this is the runtime variant
    pub fn is_runtime(&self) -> bool {
        self.variant == FunctionVariant::Runtime
    }
}

/// Function flags - bitflags for function properties
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FunctionFlags(u8);

impl FunctionFlags {
    /// Native function (has no bytecode implementation)
    pub const NATIVE: FunctionFlags = FunctionFlags(0b0001);
    /// Spec function (contains requires/ensures nodes)
    pub const SPEC: FunctionFlags = FunctionFlags(0b0010);

    pub fn new() -> Self {
        Self(0)
    }

    pub fn is_native(self) -> bool {
        self.0 & Self::NATIVE.0 != 0
    }

    pub fn is_spec(self) -> bool {
        self.0 & Self::SPEC.0 != 0
    }

    pub fn with_native(mut self) -> Self {
        self.0 |= Self::NATIVE.0;
        self
    }

    pub fn with_spec(mut self) -> Self {
        self.0 |= Self::SPEC.0;
        self
    }

    pub fn set_native(&mut self, value: bool) {
        if value {
            self.0 |= Self::NATIVE.0;
        } else {
            self.0 &= !Self::NATIVE.0;
        }
    }

    pub fn set_spec(&mut self, value: bool) {
        if value {
            self.0 |= Self::SPEC.0;
        } else {
            self.0 &= !Self::SPEC.0;
        }
    }
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Parameter {
    /// Parameter name
    pub name: String,

    /// Parameter type
    pub param_type: Type,

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
    pub return_type: Type,
}

impl FunctionSignature {
    /// Check if this function is monadic (returns Except)
    pub fn is_monadic(&self) -> bool {
        self.return_type.is_monad()
    }
}

/// A function represented as structured control flow
#[derive(Debug, Clone)]
pub struct Function {
    /// Module this function belongs to
    pub module_id: ModuleID,

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

    /// Function flags (native, spec, etc.)
    pub flags: FunctionFlags,
}

impl Function {
    /// Get mutable access to SSA registry
    pub fn variable_registry(&mut self) -> &mut VariableRegistry {
        &mut self.variables
    }

    /// Check if this function is monadic (returns Except)
    pub fn is_monadic(&self) -> bool {
        self.signature.is_monadic()
    }

    /// Check if this is a native function
    pub fn is_native(&self) -> bool {
        self.flags.is_native()
    }

    /// Check if this is a spec function
    pub fn is_spec(&self) -> bool {
        self.flags.is_spec()
    }

    /// Get the full name including variant suffix
    pub fn full_name(&self, variant: FunctionVariant) -> String {
        match variant {
            FunctionVariant::Runtime => self.name.clone(),
            FunctionVariant::Pure => format!("{}.pure", self.name),
            FunctionVariant::Aborts => format!("{}.aborts", self.name),
            FunctionVariant::Requires => format!("{}.requires", self.name),
            FunctionVariant::Ensures(0) => format!("{}.ensures", self.name),
            FunctionVariant::Ensures(n) => format!("{}.ensures_{}", self.name, n),
        }
    }

    /// Optimize the function body in place.
    ///
    /// This runs the complete optimization pipeline (see `analysis::optimize`):
    /// The pipeline runs to fix-point automatically.
    pub fn optimize(&mut self, ctx: &TypeContext) {
        self.body = analysis::optimize(self.body.clone(), ctx);
    }
}

impl Dependable for Function {
    type Id = usize; // Base ID only for dependency ordering
    type MoveKey = QualifiedId<FunId>;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        self.body.calls().into_iter().map(|id| id.base)
    }

    fn with_mutual_group_id(mut self, group_id: usize) -> Self {
        self.mutual_group_id = Some(group_id);
        self
    }
}
