// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Conversion functions between spec and implementation types

use crate::{FunctionID, Type};
use std::collections::HashMap;

/// Specification for how a type should be represented in spec functions
#[derive(Debug, Clone)]
pub struct TypeSpec {
    /// The spec representation of this type (e.g., Int for I32)
    pub spec_type: Type,
    /// Function to convert from impl type to spec type (e.g., i32_to_int)
    pub to_spec_fn: FunctionID,
    /// Function to convert from spec type to impl type (e.g., int_to_i32)
    pub from_spec_fn: FunctionID,
}

/// Registry of type specifications for spec/impl conversion
#[derive(Debug, Clone, Default)]
pub struct ConversionRegistry {
    /// Map from impl type to its spec representation
    specs: HashMap<Type, TypeSpec>,
}

impl ConversionRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a type specification
    pub fn register(&mut self, impl_type: Type, spec: TypeSpec) {
        self.specs.insert(impl_type, spec);
    }

    /// Get the spec for a type
    pub fn get(&self, impl_type: &Type) -> Option<&TypeSpec> {
        self.specs.get(impl_type)
    }

    /// Get the spec type representation for an impl type
    pub fn spec_type(&self, impl_type: &Type) -> Option<&Type> {
        self.specs.get(impl_type).map(|spec| &spec.spec_type)
    }

    /// Get the function that converts from impl to spec
    pub fn to_spec_fn(&self, impl_type: &Type) -> Option<FunctionID> {
        self.specs.get(impl_type).map(|spec| spec.to_spec_fn)
    }

    /// Get the function that converts from spec to impl
    pub fn from_spec_fn(&self, impl_type: &Type) -> Option<FunctionID> {
        self.specs.get(impl_type).map(|spec| spec.from_spec_fn)
    }

    /// Check if a type has a registered spec
    pub fn has_spec(&self, impl_type: &Type) -> bool {
        self.specs.contains_key(impl_type)
    }

    /// Convert a type from impl to spec representation recursively
    pub fn convert_to_spec_type(&self, ty: &Type) -> Type {
        // Check if this exact type has a spec
        if let Some(spec) = self.get(ty) {
            return spec.spec_type.clone();
        }

        // Recursively convert composite types
        match ty {
            Type::Vector(inner) => Type::Vector(Box::new(self.convert_to_spec_type(inner))),
            Type::Reference(inner) => Type::Reference(Box::new(self.convert_to_spec_type(inner))),
            Type::MutableReference(inner) => {
                Type::MutableReference(Box::new(self.convert_to_spec_type(inner)))
            }
            Type::Except(inner) => Type::Except(Box::new(self.convert_to_spec_type(inner))),
            Type::Tuple(tys) => {
                Type::Tuple(tys.iter().map(|t| self.convert_to_spec_type(t)).collect())
            }
            Type::Struct {
                struct_id,
                type_args,
            } => Type::Struct {
                struct_id: *struct_id,
                type_args: type_args
                    .iter()
                    .map(|t| self.convert_to_spec_type(t))
                    .collect(),
            },
            other => other.clone(),
        }
    }

    /// Check if a type needs any conversion (recursively)
    pub fn needs_conversion(&self, ty: &Type) -> bool {
        if self.has_spec(ty) {
            return true;
        }

        match ty {
            Type::Vector(inner)
            | Type::Reference(inner)
            | Type::MutableReference(inner)
            | Type::Except(inner) => self.needs_conversion(inner),
            Type::Tuple(tys) => tys.iter().any(|t| self.needs_conversion(t)),
            Type::Struct { type_args, .. } => type_args.iter().any(|t| self.needs_conversion(t)),
            _ => false,
        }
    }
}
