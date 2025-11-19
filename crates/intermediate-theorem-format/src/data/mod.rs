// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::hash::Hash;
use indexmap::IndexMap;

// Re-export type aliases from structure
pub use functions::TheoremFunctionID;
pub use structure::TheoremStructID;

pub mod expressions;
pub mod functions;
pub mod variables;
pub mod structure;
pub mod types;
pub mod statements;

/// Unique identifier for a module in the program
pub type TheoremModuleID = usize;

/// Trait for items that can have dependencies on other items of the same type
pub trait Dependable {
    type Id: Copy + Eq + Hash + Ord + std::fmt::Debug;

    /// Iterator over dependencies for this item
    fn dependencies(&self) -> impl Iterator<Item = Self::Id>;

    /// Set the mutual recursion group ID for this item
    fn with_mutual_group_id(self, group_id: usize) -> Self;
}

// ============================================================================
// Name Management
// ============================================================================

/// Names associated with a struct for code generation
#[derive(Debug, Clone)]
pub struct StructNames {
    /// Type name (e.g., "Balance")
    pub type_name: String,

    /// Module name (e.g., "IntegerMate")
    pub module_name: String,
}

/// Names associated with a module for Lean code generation
#[derive(Debug, Clone)]
pub struct ModuleNames {
    /// Qualified name with address (e.g., "0x2::balance")
    pub qualified_name: String,
}

/// Centralized name management for rendering
/// Maps IDs to their various name representations needed for code generation
#[derive(Debug, Clone)]
pub struct NameManager {
    /// Struct ID -> names
    pub struct_names: BTreeMap<TheoremStructID, StructNames>,
}

impl NameManager {
    /// Create a new empty name manager
    pub fn new() -> Self {
        Self {
            struct_names: BTreeMap::new(),
        }
    }

    /// Get struct names by ID
    /// Panics if struct ID is not registered (indicates a bug in translation)
    pub fn get_struct_names(&self, id: TheoremStructID) -> &StructNames {
        self.struct_names.get(&id)
            .expect("BUG: Struct ID not registered in NameManager")
    }

    /// Register struct names
    pub fn register_struct(&mut self, id: TheoremStructID, names: StructNames) {
        self.struct_names.insert(id, names);
    }
}

// ============================================================================
// Complete Program IR
// ============================================================================

/// Complete program representation with translated function bodies.
/// Functions and structs are stored centrally and sorted in global dependency order.
#[derive(Debug, Clone)]
pub struct TheoremProgram {
    /// All modules in the program (minimal metadata only)
    pub modules: BTreeMap<TheoremModuleID, TheoremModule>,

    /// All functions with bodies (sorted in global dependency order)
    pub functions: IndexMap<TheoremFunctionID, functions::TheoremFunction>,

    /// All structs in the program (sorted in global dependency order)
    pub structs: IndexMap<TheoremStructID, structure::TheoremStruct>,

    /// Name manager for rendering
    pub name_manager: NameManager,
}

impl TheoremProgram {
    /// Create a new empty program IR
    pub fn new() -> Self {
        Self {
            modules: BTreeMap::new(),
            functions: IndexMap::new(),
            structs: IndexMap::new(),
            name_manager: NameManager::new(),
        }
    }

    /// Get a function by ID
    pub fn get_function(&self, id: TheoremFunctionID) -> Option<&functions::TheoremFunction> {
        self.functions.get(&id)
    }

    /// Get a module by ID
    pub fn get_module(&self, id: TheoremModuleID) -> Option<&TheoremModule> {
        self.modules.get(&id)
    }
}

// ============================================================================
// Module IR
// ============================================================================

/// A module in the program (minimal metadata only - no ownership of functions/structs)
#[derive(Debug, Clone)]
pub struct TheoremModule {
    /// Unique identifier for this module
    pub id: TheoremModuleID,

    /// Module name (e.g., "0x123::math::helpers")
    pub name: String,

    /// Simple module name (last component, e.g., "helpers")
    pub simple_name: String,

    /// Package name from Move.toml (e.g., "Sui", "MoveStdlib", "DeepBook")
    pub package_name: String,
}