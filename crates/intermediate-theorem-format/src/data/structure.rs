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
    /// Unique identifier for this struct
    pub id: TheoremStructID,

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

    fn dependencies(&self) -> impl Iterator<Item = Self::Id> {
        // Collect all struct IDs from all fields, recursively through type constructors
        let mut deps = Vec::new();
        for field in &self.fields {
            Self::collect_struct_deps(&field.field_type, &mut deps);
        }
        deps.into_iter()
    }

    fn with_mutual_group_id(mut self, group_id: usize) -> Self {
        self.mutual_group_id = Some(group_id);
        self
    }
}

impl TheoremStruct {
    /// Recursively collect all struct IDs from a type
    fn collect_struct_deps(ty: &TheoremType, deps: &mut Vec<TheoremStructID>) {
        match ty {
            TheoremType::Struct { struct_id, type_args } => {
                deps.push(*struct_id);
                for arg in type_args {
                    Self::collect_struct_deps(arg, deps);
                }
            }
            TheoremType::Vector(elem) => {
                Self::collect_struct_deps(elem, deps);
            }
            TheoremType::Reference(inner) | TheoremType::MutableReference(inner) => {
                Self::collect_struct_deps(inner, deps);
            }
            TheoremType::Tuple(types) => {
                for ty in types {
                    Self::collect_struct_deps(ty, deps);
                }
            }
            TheoremType::ProgramState(inner) => {
                Self::collect_struct_deps(inner, deps);
            }
            _ => {}
        }
    }
}