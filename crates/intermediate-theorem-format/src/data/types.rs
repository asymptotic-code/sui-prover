// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Type system for TheoremIR

use move_model::ty::{PrimitiveType, Type};
use move_model::model::{GlobalEnv, QualifiedId, DatatypeId};
use std::collections::BTreeMap;
use crate::TheoremStructID;

/// Temporary value identifier (SSA form)
pub type TempId = u32;

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
    /// ProgramState monad wrapping a type (for abort handling)
    ProgramState(Box<TheoremType>),
}

impl TheoremType {
    /// Create from Move model type with eager ID resolution
    ///
    /// # Panics
    /// Panics if a struct type is not found in struct_id_map, which indicates
    /// a bug in the translation pipeline (structs must be registered before use)
    pub fn from_move_type(
        ty: &Type,
        env: &GlobalEnv,
        struct_id_map: &BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
    ) -> Self {
        match ty {
            Type::Primitive(PrimitiveType::Bool) => TheoremType::Bool,
            Type::Primitive(PrimitiveType::U8) => TheoremType::UInt(8),
            Type::Primitive(PrimitiveType::U16) => TheoremType::UInt(16),
            Type::Primitive(PrimitiveType::U32) => TheoremType::UInt(32),
            Type::Primitive(PrimitiveType::U64) => TheoremType::UInt(64),
            Type::Primitive(PrimitiveType::U128) => TheoremType::UInt(128),
            Type::Primitive(PrimitiveType::U256) => TheoremType::UInt(256),
            Type::Primitive(PrimitiveType::Address) => TheoremType::Address,
            Type::Primitive(PrimitiveType::Signer) => TheoremType::Address,
            Type::Datatype(module_id, struct_id, type_args) => {
                let qualified_id = module_id.qualified(*struct_id);

                // Lookup the TheoremStructID - fail fast if not found
                let theorem_struct_id = *struct_id_map.get(&qualified_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "BUG: Datatype must be registered in struct_id_map before type translation. \
                             QualifiedId: {:?}, Total registered datatypes: {}",
                            qualified_id,
                            struct_id_map.len()
                        )
                    });

                // Recursively resolve type arguments
                let resolved_type_args: Vec<TheoremType> = type_args.iter()
                    .map(|arg| Self::from_move_type(arg, env, struct_id_map))
                    .collect();

                TheoremType::Struct {
                    struct_id: theorem_struct_id,
                    type_args: resolved_type_args,
                }
            }
            Type::Vector(elem_ty) => {
                TheoremType::Vector(Box::new(Self::from_move_type(elem_ty, env, struct_id_map)))
            }
            Type::Reference(_, ty) => {
                TheoremType::Reference(Box::new(Self::from_move_type(ty, env, struct_id_map)))
            }
            Type::TypeParameter(idx) => TheoremType::TypeParameter(*idx),
            Type::Tuple(tys) => {
                TheoremType::Tuple(tys.iter().map(|t| Self::from_move_type(t, env, struct_id_map)).collect())
            }
            _ => unreachable!(),
        }
    }

    /// Wrap this type in ProgramState monad
    pub fn wrap_in_monad(self) -> Self {
        TheoremType::ProgramState(Box::new(self))
    }

    /// Check if this is a ProgramState type
    pub fn is_monad(&self) -> bool {
        matches!(self, TheoremType::ProgramState(_))
    }

    /// Unwrap the inner type from ProgramState, if applicable
    pub fn unwrap_monad(&self) -> Option<&TheoremType> {
        match self {
            TheoremType::ProgramState(inner) => Some(inner),
            _ => None,
        }
    }

    /// Sanitize a name for use in Lean identifiers
    pub fn sanitize_name(name: &str) -> String {
        name.replace("::", "_")
            .replace("<", "")
            .replace(">", "")
            .replace("$", "_")
            .replace("%", "_")
            .replace("#", "_")
            .replace("@", "_")
            .chars()
            .filter(|c| c.is_alphanumeric() || *c == '_')
            .collect()
    }

    // ========================================================================
    // Functional Traversal API (Visitor Pattern)
    // ========================================================================

    /// Fold over all types in the type tree (pre-order traversal)
    /// The closure receives the accumulator and a reference to each type
    pub fn fold<T>(&self, init: T, mut f: impl FnMut(T, &TheoremType) -> T) -> T {
        self.fold_impl(init, &mut f)
    }

    fn fold_impl<T>(&self, acc: T, f: &mut impl FnMut(T, &TheoremType) -> T) -> T {
        // First apply function to current type
        let acc = f(acc, self);

        // Then recursively fold over child types
        match self {
            TheoremType::Struct { type_args, .. } => {
                type_args.iter().fold(acc, |acc, ty| ty.fold_impl(acc, f))
            }
            TheoremType::Vector(inner) |
            TheoremType::Reference(inner) |
            TheoremType::MutableReference(inner) |
            TheoremType::ProgramState(inner) => {
                inner.fold_impl(acc, f)
            }
            TheoremType::Tuple(types) => {
                types.iter().fold(acc, |acc, ty| ty.fold_impl(acc, f))
            }
            TheoremType::Bool |
            TheoremType::UInt(_) |
            TheoremType::SInt(_) |
            TheoremType::Address |
            TheoremType::TypeParameter(_) => {
                // Leaf nodes, just return accumulator
                acc
            }
        }
    }

    /// Map over the type tree, transforming each type
    pub fn map(&self, f: &impl Fn(&TheoremType) -> TheoremType) -> TheoremType {
        let transformed = match self {
            TheoremType::Struct { struct_id, type_args } => {
                TheoremType::Struct {
                    struct_id: *struct_id,
                    type_args: type_args.iter().map(|t| t.map(f)).collect(),
                }
            }
            TheoremType::Vector(inner) => {
                TheoremType::Vector(Box::new(inner.map(f)))
            }
            TheoremType::Reference(inner) => {
                TheoremType::Reference(Box::new(inner.map(f)))
            }
            TheoremType::MutableReference(inner) => {
                TheoremType::MutableReference(Box::new(inner.map(f)))
            }
            TheoremType::ProgramState(inner) => {
                TheoremType::ProgramState(Box::new(inner.map(f)))
            }
            TheoremType::Tuple(types) => {
                TheoremType::Tuple(types.iter().map(|t| t.map(f)).collect())
            }
            // Leaf types - just clone
            ty @ (TheoremType::Bool |
            TheoremType::UInt(_) |
            TheoremType::SInt(_) |
            TheoremType::Address |
            TheoremType::TypeParameter(_)) => ty.clone(),
        };

        // Apply transformation function to the result
        f(&transformed)
    }

    /// Iterate over all types in the type tree
    pub fn for_each(&self, mut f: impl FnMut(&TheoremType)) {
        self.for_each_impl(&mut f);
    }

    fn for_each_impl(&self, f: &mut impl FnMut(&TheoremType)) {
        f(self);
        match self {
            TheoremType::Struct { type_args, .. } => {
                for ty in type_args {
                    ty.for_each_impl(f);
                }
            }
            TheoremType::Vector(inner) |
            TheoremType::Reference(inner) |
            TheoremType::MutableReference(inner) |
            TheoremType::ProgramState(inner) => {
                inner.for_each_impl(f);
            }
            TheoremType::Tuple(types) => {
                for ty in types {
                    ty.for_each_impl(f);
                }
            }
            _ => {}
        }
    }

    /// Collect all types matching a predicate
    pub fn collect<T>(&self, mut predicate: impl FnMut(&TheoremType) -> Option<T>) -> Vec<T> {
        let mut results = Vec::new();
        self.for_each(|ty| {
            if let Some(value) = predicate(ty) {
                results.push(value);
            }
        });
        results
    }

    /// Collect all struct IDs in the type tree
    pub fn collect_struct_ids(&self) -> Vec<TheoremStructID> {
        self.collect(|ty| {
            if let TheoremType::Struct { struct_id, .. } = ty {
                Some(*struct_id)
            } else {
                None
            }
        })
    }

    /// Check if any type in the tree satisfies a predicate
    pub fn any(&self, mut predicate: impl FnMut(&TheoremType) -> bool) -> bool {
        self.fold(false, |acc, ty| acc || predicate(ty))
    }

    /// Check if all types in the tree satisfy a predicate
    pub fn all(&self, mut predicate: impl FnMut(&TheoremType) -> bool) -> bool {
        self.fold(true, |acc, ty| acc && predicate(ty))
    }

    /// Check if this type contains any struct types
    pub fn contains_struct(&self) -> bool {
        self.any(|ty| matches!(ty, TheoremType::Struct { .. }))
    }

    /// Check if this type contains any type parameters
    pub fn contains_type_parameter(&self) -> bool {
        self.any(|ty| matches!(ty, TheoremType::TypeParameter(_)))
    }
}
