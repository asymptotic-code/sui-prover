// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! SSA Registry - Single source of truth for SSA temporary variables
//!
//! This module provides a centralized registry for all variables in a function.
//! It tracks names, types, and definitions for each temp.

use crate::data::types::{TempId, TheoremType};
use std::collections::BTreeMap;

/// Registry for variables
///
/// Single source of truth for all temporary variables in a function.
/// Stores names, types, and optionally definitions.
#[derive(Default, Debug, Clone)]
pub struct VariableRegistry {
    /// Maps temp ID to its user-friendly name
    names: BTreeMap<TempId, String>,

    /// Maps temp ID to its type
    types: BTreeMap<TempId, TheoremType>,
}

impl VariableRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self {
            names: BTreeMap::new(),
            types: BTreeMap::new(),
        }
    }
    
    /// Get the name for a temporary
    pub fn get_name(&self, temp: TempId) -> Option<&str> {
        self.names.get(&temp).map(|s| s.as_str())
    }

    /// Get the type for a temporary
    pub fn get_type(&self, temp: TempId) -> Option<&TheoremType> {
        self.types.get(&temp)
    }

    /// Register a new temporary with name and type
    pub fn register(&mut self, temp: TempId, name: String, ty: TheoremType) {
        self.names.insert(temp, name);
        self.types.insert(temp, ty);
    }

    /// Set the name for a temporary
    pub fn set_name(&mut self, temp: TempId, name: String) {
        self.names.insert(temp, name);
    }

    /// Set the type for a temporary
    pub fn set_type(&mut self, temp: TempId, ty: TheoremType) {
        self.types.insert(temp, ty);
    }

    /// Get all registered temp IDs
    pub fn all_temps(&self) -> Vec<TempId> {
        let mut temps: Vec<_> = self.names.keys().copied().collect();
        temps.sort();
        temps
    }
}
