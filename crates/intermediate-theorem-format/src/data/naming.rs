// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Name management for code generation
//!
//! Centralized naming system that maps IDs to their various name representations
//! needed for backend code generation.

use std::collections::BTreeMap;
use crate::data::TheoremStructID;

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
    struct_names: BTreeMap<TheoremStructID, StructNames>,
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
