// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Variable Registry - Single source of truth for variable metadata
//!
//! Variables are identified by index (usize) but converted to names (TempId) for IR.

use crate::data::types::TheoremType;
use std::collections::BTreeMap;

/// Registry for variables - single source of truth
///
/// Maps variable indices to their types. Generates names like "$t0", "$t1", etc.
#[derive(Debug, Clone)]
pub struct VariableRegistry {
    variables: BTreeMap<usize, TheoremType>,
}

impl VariableRegistry {
    pub fn new(variables: BTreeMap<usize, TheoremType>) -> Self {
        Self { variables }
    }

    /// Get the type for a variable
    pub fn get_type(&self, index: usize) -> Option<&TheoremType> {
        self.variables.get(&index)
    }

    /// Check if a variable is registered
    pub fn contains(&self, index: usize) -> bool {
        self.variables.contains_key(&index)
    }

    /// Iterate over all variables (index, type)
    pub fn iter(&self) -> impl Iterator<Item = (usize, &TheoremType)> {
        self.variables.iter().map(|(&k, v)| (k, v))
    }
    
    pub fn is_temp(name: &str) -> bool {
        name.chars().next().unwrap_or('a') == '$'
    }
}
