// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Struct IR data structures

use crate::data::types::TheoremType;
use crate::data::Dependable;
use crate::TheoremModuleID;

/// Unique identifier for a struct in the program
pub type TheoremStructID = usize;

// ============================================================================
// Struct IR
// ============================================================================

/// A struct definition
#[derive(Debug, Clone)]
pub struct TheoremStruct {
    /// The struct's module
    pub module_id: TheoremModuleID,

    /// Struct name
    pub name: String,

    /// Full qualified name
    pub qualified_name: String,

    /// Type parameters
    pub type_params: Vec<String>,

    /// Fields
    pub fields: Vec<TheoremField>,

    /// Mutual recursion group ID (None if not mutually recursive)
    /// Structs with the same group ID are mutually recursive and must be defined together
    pub mutual_group_id: Option<usize>,
}

/// A field in a struct
#[derive(Debug, Clone)]
pub struct TheoremField {
    /// Field name
    pub name: String,

    /// Field type
    pub field_type: TheoremType,
}

impl Dependable for TheoremStruct {
    type Id = TheoremStructID;
    type MoveKey = move_model::model::QualifiedId<move_model::model::DatatypeId>;

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        self.fields.iter()
            .flat_map(|field| field.field_type.struct_ids())
    }

    fn with_mutual_group_id(mut self, group_id: usize) -> Self {
        self.mutual_group_id = Some(group_id);
        self
    }
}