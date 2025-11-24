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

    /// Get a mutable reference to a module by ID
    pub fn get_module_mut(&mut self, id: TheoremModuleID) -> &mut TheoremModule {
        self.modules.get_mut(&id).expect("Module should exist")
    }

    /// Get the module ID for a struct
    pub fn get_struct_module(&self, struct_id: TheoremStructID) -> TheoremModuleID {
        self.structs.get(&struct_id).expect("Struct should exist").module_id
    }

    /// Get the module ID for a function
    pub fn get_function_module(&self, function_id: TheoremFunctionID) -> TheoremModuleID {
        self.functions.get(&function_id).expect("Function should exist").module_id
    }

    /// Iterator over all modules
    pub fn modules(&self) -> impl Iterator<Item = &TheoremModule> {
        self.modules.values()
    }

    /// Iterator over all functions
    pub fn functions(&self) -> impl Iterator<Item = &functions::TheoremFunction> {
        self.functions.values()
    }

    /// Iterator over all structs
    pub fn structs(&self) -> impl Iterator<Item = &structure::TheoremStruct> {
        self.structs.values()
    }

    /// Create TheoremProgram from LazyIdBuilder
    ///
    /// This converts construction data into final IR and runs analysis passes
    pub fn from_builder(builder: crate::lazy_builder::LazyIdBuilder) -> Self {
        use crate::analysis::{DependencyOrderPass, ImportCollectionPass};

        let mut program = Self::new();
        program.name_manager = builder.name_manager;

        // Build modules
        for (module_id, construction) in builder.modules {
            let module = TheoremModule {
                id: module_id,
                name: construction.name,
                package_name: construction.package_name,
                required_imports: Vec::new(), // Filled by ImportCollectionPass
            };
            program.modules.insert(module_id, module);
        }

        // Build structs
        for (struct_id, construction) in builder.structs {
            let theorem_struct = structure::TheoremStruct {
                id: struct_id,
                module_id: builder.module_structs.iter()
                    .find(|(_, structs)| structs.contains(&struct_id))
                    .map(|(mid, _)| *mid)
                    .expect("Every struct should belong to a module"),
                name: construction.name,
                qualified_name: construction.qualified_name,
                type_params: construction.type_params,
                fields: construction.fields,
                mutual_group_id: None, // Filled by DependencyOrderPass
            };
            program.structs.insert(struct_id, theorem_struct);
        }

        // Build functions
        for (function_id, construction) in builder.functions {
            let theorem_function = functions::TheoremFunction {
                id: function_id,
                module_id: builder.module_functions.iter()
                    .find(|(_, functions)| functions.contains(&function_id))
                    .map(|(mid, _)| *mid)
                    .expect("Every function should belong to a module"),
                name: construction.name,
                signature: construction.signature,
                body: construction.body,
                ssa_registry: construction.ssa_registry,
                mutual_group_id: None, // Filled by DependencyOrderPass
                is_native: construction.is_native,
            };
            program.functions.insert(function_id, theorem_function);
        }

        // Run analysis passes
        eprintln!("Running DependencyOrderPass...");
        DependencyOrderPass::run(&mut program);
        eprintln!("Running ImportCollectionPass...");
        ImportCollectionPass::run(&mut program);
        eprintln!("Analysis passes complete!");

        program
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

    /// Module name (last component, e.g., "helpers")
    pub name: String,

    /// Package name from Move.toml (e.g., "Sui", "MoveStdlib", "DeepBook")
    pub package_name: String,

    /// Required imports for this module (computed during IR construction)
    /// Contains TheoremModuleIDs of modules that this module depends on
    pub required_imports: Vec<TheoremModuleID>,
}