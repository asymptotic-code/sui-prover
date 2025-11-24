// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lazy ID builder for TheoremProgram construction
//!
//! Creates IDs on-demand as elements are added, storing construction data.
//! TheoremProgram::from_builder validates all IDs have data.

use crate::construction::{FunctionConstruction, ModuleConstruction, StructConstruction};
use crate::{NameManager, TheoremFunctionID, TheoremModuleID, TheoremStructID};
use move_model::model::{DatatypeId, FunId, ModuleId, QualifiedId};
use std::collections::BTreeMap;

/// Builder that creates IDs lazily and stores construction data
pub struct LazyIdBuilder {
    // ID allocation
    next_module_id: usize,
    next_struct_id: usize,
    next_function_id: usize,

    // Key -> ID mappings
    module_ids: BTreeMap<ModuleId, TheoremModuleID>,
    struct_ids: BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
    function_ids: BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,

    // ID -> Construction data
    pub modules: BTreeMap<TheoremModuleID, ModuleConstruction>,
    pub structs: BTreeMap<TheoremStructID, StructConstruction>,
    pub functions: BTreeMap<TheoremFunctionID, FunctionConstruction>,

    // Module ownership tracking
    pub module_structs: BTreeMap<TheoremModuleID, Vec<TheoremStructID>>,
    pub module_functions: BTreeMap<TheoremModuleID, Vec<TheoremFunctionID>>,

    // Name manager
    pub name_manager: NameManager,
}

impl LazyIdBuilder {
    pub fn new() -> Self {
        Self {
            next_module_id: 0,
            next_struct_id: 0,
            next_function_id: 0,
            module_ids: BTreeMap::new(),
            struct_ids: BTreeMap::new(),
            function_ids: BTreeMap::new(),
            modules: BTreeMap::new(),
            structs: BTreeMap::new(),
            functions: BTreeMap::new(),
            module_structs: BTreeMap::new(),
            module_functions: BTreeMap::new(),
            name_manager: NameManager::new(),
        }
    }

    /// Get or create module ID
    pub fn get_or_create_module_id(&mut self, key: ModuleId) -> TheoremModuleID {
        if let Some(&id) = self.module_ids.get(&key) {
            return id;
        }
        let id = self.next_module_id;
        self.next_module_id += 1;
        self.module_ids.insert(key, id);
        id
    }

    /// Get or create struct ID
    pub fn get_or_create_struct_id(&mut self, key: QualifiedId<DatatypeId>) -> TheoremStructID {
        if let Some(&id) = self.struct_ids.get(&key) {
            return id;
        }
        let id = self.next_struct_id;
        self.next_struct_id += 1;
        self.struct_ids.insert(key, id);
        id
    }

    /// Get or create function ID
    pub fn get_or_create_function_id(&mut self, key: QualifiedId<FunId>) -> TheoremFunctionID {
        if let Some(&id) = self.function_ids.get(&key) {
            return id;
        }
        let id = self.next_function_id;
        self.next_function_id += 1;
        self.function_ids.insert(key, id);
        id
    }

    /// Add module construction data
    pub fn add_module(&mut self, id: TheoremModuleID, construction: ModuleConstruction) {
        self.modules.insert(id, construction);
    }

    /// Add struct construction data
    pub fn add_struct(
        &mut self,
        id: TheoremStructID,
        module_id: TheoremModuleID,
        construction: StructConstruction,
    ) {
        self.structs.insert(id, construction);
        self.module_structs.entry(module_id).or_default().push(id);
    }

    /// Add function construction data
    pub fn add_function(
        &mut self,
        id: TheoremFunctionID,
        module_id: TheoremModuleID,
        construction: FunctionConstruction,
    ) {
        self.functions.insert(id, construction);
        self.module_functions.entry(module_id).or_default().push(id);
    }

    /// Get mutable access to name manager
    pub fn name_manager_mut(&mut self) -> &mut NameManager {
        &mut self.name_manager
    }
}

impl Default for LazyIdBuilder {
    fn default() -> Self {
        Self::new()
    }
}
