// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Type system for TheoremIR

use crate::TheoremStructID;

/// Temporary value identifier
pub type TempId = String;

/// Theorem IR type with enriched metadata for code generation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TheoremType {
    /// Boolean
    Bool,
    /// Unsigned integer with bit width
    UInt(u32),
    /// Signed integer with bit width
    SInt(u32),
    /// Address
    Address,
    /// Struct type
    /// Names are looked up via NameManager during rendering
    Struct {
        /// Unique struct ID in the TheoremProgram
        /// Used to lookup names via NameManager and struct definitions
        struct_id: TheoremStructID,
        /// Type arguments (for generics like Coin<SUI>)
        type_args: Vec<TheoremType>,
    },
    /// Vector of elements
    Vector(Box<TheoremType>),
    /// Reference (immutable)
    Reference(Box<TheoremType>),
    /// Mutable reference
    MutableReference(Box<TheoremType>),
    /// Type parameter
    TypeParameter(u16),
    /// Tuple
    Tuple(Vec<TheoremType>),
    /// Except monad wrapping a type (for abort handling)
    /// Represents an error monad for capturing abort codes
    Except(Box<TheoremType>),
}

impl TheoremType {
    /// Wrap this type in Except monad
    pub fn wrap_in_monad(self) -> Self {
        TheoremType::Except(Box::new(self))
    }

    /// Check if this is an Except type
    pub fn is_monad(&self) -> bool {
        matches!(self, TheoremType::Except(_))
    }

    /// Unwrap the inner type from Except, if applicable
    pub fn unwrap_monad(&self) -> Option<&TheoremType> {
        match self {
            TheoremType::Except(inner) => Some(inner),
            _ => None,
        }
    }

    /// Collect all struct IDs referenced in this type
    pub fn struct_ids(&self) -> Vec<TheoremStructID> {
        let mut ids = Vec::new();
        self.collect_struct_ids(&mut ids);
        ids
    }

    fn collect_struct_ids(&self, ids: &mut Vec<TheoremStructID>) {
        match self {
            TheoremType::Struct { struct_id, type_args } => {
                ids.push(*struct_id);
                type_args.iter().for_each(|t| t.collect_struct_ids(ids));
            }
            TheoremType::Vector(inner) | TheoremType::Reference(inner) |
            TheoremType::MutableReference(inner) | TheoremType::Except(inner) => {
                inner.collect_struct_ids(ids);
            }
            TheoremType::Tuple(tys) => {
                tys.iter().for_each(|t| t.collect_struct_ids(ids));
            }
            TheoremType::Bool | TheoremType::UInt(_) | TheoremType::SInt(_) |
            TheoremType::Address | TheoremType::TypeParameter(_) => {}
        }
    }
}
