// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! SSA Registry - Single source of truth for SSA temporary variables
//!
//! This module provides a centralized registry for all variables in a function.
//! All metadata is required at allocation time, preventing edge cases from
//! forgetting to track phi relationships or variable types.

use crate::data::types::{TempId, TheoremType};
use std::collections::BTreeMap;

/// Default base ID for VariableRegistry, high enough to avoid collision with bytecode temps.
/// Move bytecode typically uses small integers (0, 1, 2, ...) for local temps.
pub const DEFAULT_REGISTRY_BASE_ID: TempId = 1000;

/// Kind of temporary variable - tracks phi relationships structurally
#[derive(Debug, Clone)]
pub enum TempKind {
    /// Regular local variable or parameter
    Local,
    /// Phi from if-merge - tracks what it merges
    IfPhi {
        /// The original variable (by TempId) this phi is merging
        /// This is the "root" variable before any phi transformations
        original: TempId,
        /// Source temp from the then-branch
        then_src: TempId,
        /// Source temp from the else-branch
        else_src: TempId,
    },
    /// Phi from loop - tracks loop-carried variable
    LoopPhi {
        /// The original variable this loop phi is tracking
        original: TempId,
        /// Initial value before loop starts
        initial: TempId,
        /// Updated value at end of loop body
        updated: TempId,
    },
}

/// All data for a single temporary variable - required at allocation time
#[derive(Debug, Clone)]
pub struct TempData {
    /// Type of the variable
    pub ty: TheoremType,
    /// User-friendly name
    pub name: String,
    /// Kind (local, if-phi, loop-phi) with structural tracking
    pub kind: TempKind,
}

/// Registry for variables - single source of truth
///
/// All temporary variables in a function must be allocated through this registry.
/// - Bytecode temps (IDs < base_id): Use `register_bytecode_temp()` for Move locals
/// - Generated temps (IDs >= base_id): Use `alloc_local()`, `alloc_if_phi()`, `alloc_loop_phi()`
#[derive(Default, Debug, Clone)]
pub struct VariableRegistry {
    /// Storage for registry-allocated temps (IDs >= base_id) - TempId - base_id is index
    temps: Vec<TempData>,
    /// Offset for TempIds (to avoid collision with bytecode temps)
    base_id: TempId,
    /// Storage for bytecode temps (IDs < base_id)
    bytecode_temps: BTreeMap<TempId, TempData>,
}

impl VariableRegistry {
    /// Create a new empty registry with default base ID
    pub fn new() -> Self {
        Self::with_base_id(DEFAULT_REGISTRY_BASE_ID)
    }

    /// Create a registry with a specific base ID
    pub fn with_base_id(base_id: TempId) -> Self {
        Self {
            temps: Vec::new(),
            base_id,
            bytecode_temps: BTreeMap::new(),
        }
    }

    /// Allocate a new temp with all required metadata
    /// This is the ONLY way to create temps - ensures no metadata is forgotten
    pub fn alloc(&mut self, name: String, ty: TheoremType, kind: TempKind) -> TempId {
        let id = self.base_id + self.temps.len() as TempId;
        self.temps.push(TempData { ty, name, kind });
        id
    }

    /// Allocate a local (non-phi) temp
    pub fn alloc_local(&mut self, name: String, ty: TheoremType) -> TempId {
        self.alloc(name, ty, TempKind::Local)
    }

    /// Allocate an if-phi temp
    pub fn alloc_if_phi(
        &mut self,
        name: String,
        ty: TheoremType,
        original: TempId,
        then_src: TempId,
        else_src: TempId,
    ) -> TempId {
        self.alloc(name, ty, TempKind::IfPhi { original, then_src, else_src })
    }

    /// Allocate a loop-phi temp
    pub fn alloc_loop_phi(
        &mut self,
        name: String,
        ty: TheoremType,
        original: TempId,
        initial: TempId,
        updated: TempId,
    ) -> TempId {
        self.alloc(name, ty, TempKind::LoopPhi { original, initial, updated })
    }

    /// Get the data for a temp (checks both registry temps and bytecode temps)
    pub fn get(&self, id: TempId) -> Option<&TempData> {
        if id < self.base_id {
            self.bytecode_temps.get(&id)
        } else {
            self.temps.get((id - self.base_id) as usize)
        }
    }

    /// Get mutable data for a temp
    pub fn get_mut(&mut self, id: TempId) -> Option<&mut TempData> {
        if id < self.base_id {
            self.bytecode_temps.get_mut(&id)
        } else {
            self.temps.get_mut((id - self.base_id) as usize)
        }
    }

    /// Get the name for a temporary
    /// Returns None if name is empty (created by set_type without a name)
    pub fn get_name(&self, temp: TempId) -> Option<&str> {
        self.get(temp)
            .map(|d| d.name.as_str())
            .filter(|s| !s.is_empty())
    }

    /// Get the type for a temporary
    pub fn get_type(&self, temp: TempId) -> Option<&TheoremType> {
        self.get(temp).map(|d| &d.ty)
    }

    /// Get the kind for a temporary
    pub fn get_kind(&self, temp: TempId) -> Option<&TempKind> {
        self.get(temp).map(|d| &d.kind)
    }

    /// Follow phi chain to find root variable
    /// Returns the original non-phi temp that this phi derives from
    pub fn root(&self, id: TempId) -> TempId {
        match self.get_kind(id) {
            Some(TempKind::IfPhi { original, .. }) | Some(TempKind::LoopPhi { original, .. }) => {
                self.root(*original)
            }
            _ => id, // Local or not in registry - return as-is
        }
    }

    /// Get the root name (original variable name without phi prefixes)
    pub fn root_name(&self, id: TempId) -> Option<&str> {
        let root_id = self.root(id);
        self.get_name(root_id)
    }

    /// Get the canonical name for a temp (root_name if available, otherwise get_name)
    /// This is the standard way to get a variable's logical name for tracking.
    pub fn canonical_name(&self, id: TempId) -> Option<&str> {
        self.root_name(id).or_else(|| self.get_name(id))
    }

    /// Check if this temp is any kind of phi
    pub fn is_phi(&self, id: TempId) -> bool {
        matches!(
            self.get_kind(id),
            Some(TempKind::IfPhi { .. }) | Some(TempKind::LoopPhi { .. })
        )
    }

    /// Check if this temp is an if-phi
    pub fn is_if_phi(&self, id: TempId) -> bool {
        matches!(self.get_kind(id), Some(TempKind::IfPhi { .. }))
    }

    /// Check if this temp is a loop-phi
    pub fn is_loop_phi(&self, id: TempId) -> bool {
        matches!(self.get_kind(id), Some(TempKind::LoopPhi { .. }))
    }

    /// Get all registered temp IDs
    pub fn all_temps(&self) -> Vec<TempId> {
        (0..self.temps.len() as TempId)
            .map(|i| self.base_id + i)
            .collect()
    }

    /// Get the display name for a temporary (for code generation)
    /// Returns the registered name if available, otherwise generates t{id}
    pub fn get_display_name(&self, temp: TempId) -> String {
        self.get_name(temp)
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("t{}", temp))
    }

    /// Register a bytecode temp (ID < base_id) with name and type.
    /// Used for Move locals that have fixed IDs from the bytecode.
    pub fn register_bytecode_temp(&mut self, temp: TempId, name: String, ty: TheoremType) {
        assert!(temp < self.base_id, "register_bytecode_temp only for temps with ID < base_id");
        self.bytecode_temps.insert(temp, TempData {
            name,
            ty,
            kind: TempKind::Local,
        });
    }

    /// Check if a bytecode temp is already registered
    pub fn has_bytecode_temp(&self, temp: TempId) -> bool {
        temp < self.base_id && self.bytecode_temps.contains_key(&temp)
    }
}
