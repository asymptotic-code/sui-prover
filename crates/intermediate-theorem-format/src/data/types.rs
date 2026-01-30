// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Type system for TheoremIR

use crate::StructID;

/// Temporary value identifier
pub type TempId = String;

/// Theorem IR type with enriched metadata for code generation
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Boolean - computational boolean type (rendered as Bool in Lean)
    Bool,
    /// Proposition - logical type for specifications (rendered as Prop in Lean)
    /// Used in .aborts, .requires, .ensures functions
    Prop,
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
        struct_id: StructID,
        /// Type arguments (for generics like Coin<SUI>)
        type_args: Vec<Type>,
    },
    /// Vector of elements
    Vector(Box<Type>),
    /// Reference (immutable)
    Reference(Box<Type>),
    /// Mutable reference
    MutableReference(Box<Type>),
    /// Type parameter
    TypeParameter(u16),
    /// Tuple
    Tuple(Vec<Type>),
    /// Except monad wrapping a type (for abort handling)
    /// Represents an error monad for capturing abort codes
    Except(Box<Type>),
}

impl Type {
    /// Wrap this type in Except monad
    pub fn wrap_in_monad(self) -> Self {
        Type::Except(Box::new(self))
    }

    /// Check if this is an Except type
    pub fn is_monad(&self) -> bool {
        matches!(self, Type::Except(_))
    }

    /// Unwrap the inner type from Except, if applicable
    pub fn unwrap_monad(&self) -> Option<&Type> {
        match self {
            Type::Except(inner) => Some(inner),
            _ => None,
        }
    }

    /// Unwraps if the type is a monad, or else returns the type
    pub fn base_type(&self) -> Type {
        self.unwrap_monad().cloned().unwrap_or_else(|| self.clone())
    }

    /// Collect all struct IDs referenced in this type
    pub fn struct_ids(&self) -> Vec<StructID> {
        let mut ids = Vec::new();
        self.collect_struct_ids(&mut ids);
        ids
    }

    fn collect_struct_ids(&self, ids: &mut Vec<StructID>) {
        match self {
            Type::Struct {
                struct_id,
                type_args,
            } => {
                ids.push(*struct_id);
                type_args.iter().for_each(|t| t.collect_struct_ids(ids));
            }
            Type::Vector(inner)
            | Type::Reference(inner)
            | Type::MutableReference(inner)
            | Type::Except(inner) => {
                inner.collect_struct_ids(ids);
            }
            Type::Tuple(tys) => {
                tys.iter().for_each(|t| t.collect_struct_ids(ids));
            }
            Type::Bool
            | Type::Prop
            | Type::UInt(_)
            | Type::SInt(_)
            | Type::Address
            | Type::TypeParameter(_) => {}
        }
    }

    /// Check if this type contains Bool anywhere (including in tuples)
    /// Bool becomes Prop in Lean, which affects Decidable instance derivation
    pub fn contains_bool(&self) -> bool {
        match self {
            Type::Bool => true,
            Type::Tuple(tys) => tys.iter().any(|t| t.contains_bool()),
            Type::Vector(inner)
            | Type::Reference(inner)
            | Type::MutableReference(inner)
            | Type::Except(inner) => inner.contains_bool(),
            Type::Struct { type_args, .. } => type_args.iter().any(|t| t.contains_bool()),
            Type::Prop | Type::UInt(_) | Type::SInt(_) | Type::Address | Type::TypeParameter(_) => {
                false
            }
        }
    }

    /// Check if this is a Bool type
    pub fn is_bool(&self) -> bool {
        matches!(self, Type::Bool)
    }

    /// Check if this is a Prop type
    pub fn is_prop(&self) -> bool {
        matches!(self, Type::Prop)
    }
}
