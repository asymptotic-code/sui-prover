// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Struct IR data structures

use crate::data::types::Type;
use crate::data::Dependable;
use crate::ModuleID;
use move_model::model::{DatatypeId, QualifiedId};

/// Unique identifier for a struct in the program
pub type StructID = usize;

// ============================================================================
// Struct IR
// ============================================================================

/// A struct definition
#[derive(Debug, Clone)]
pub struct Struct {
    /// The struct's module
    pub module_id: ModuleID,

    /// Struct name
    pub name: String,

    /// Full qualified name
    pub qualified_name: String,

    /// Type parameters
    pub type_params: Vec<String>,

    /// Fields
    pub fields: Vec<Field>,

    /// Mutual recursion group ID (None if not mutually recursive)
    /// Structs with the same group ID are mutually recursive and must be defined together
    pub mutual_group_id: Option<usize>,
}

/// A field in a struct
#[derive(Debug, Clone)]
pub struct Field {
    /// Field name
    pub name: String,

    /// Field type
    pub field_type: Type,
}

impl Dependable for Struct {
    type Id = StructID;
    type MoveKey = QualifiedId<DatatypeId>;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        self.fields
            .iter()
            .flat_map(|field| field.field_type.struct_ids())
    }

    fn with_mutual_group_id(mut self, group_id: usize) -> Self {
        self.mutual_group_id = Some(group_id);
        self
    }
}
