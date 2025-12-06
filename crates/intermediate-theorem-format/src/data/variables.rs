// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Variable Registry and Type Context - type information for IR nodes
//!
//! Variables are identified by TempId (string names like "$t0", "x", etc.)

use crate::data::types::{TempId, Type};
use crate::data::structure::{Struct, StructID};
use crate::{FunctionID, FunctionSignature};
use std::collections::BTreeMap;

/// Maps variable names (TempId) to their types.
#[derive(Debug, Clone, Default)]
pub struct VariableRegistry {
    variables: BTreeMap<TempId, Type>,
}

impl VariableRegistry {
    pub fn new(variables: BTreeMap<TempId, Type>) -> Self {
        Self { variables }
    }

    /// Get the type for a variable by name
    pub fn get_type(&self, name: &str) -> Option<&Type> {
        self.variables.get(name)
    }

    /// Get the type for a variable, panicking if not found
    pub fn get_type_or_panic(&self, name: &str) -> &Type {
        self.variables.get(name).unwrap_or_else(|| {
            panic!("Variable '{}' not found in registry. Available: {:?}",
                   name, self.variables.keys().collect::<Vec<_>>())
        })
    }

    /// Register a variable with its type
    pub fn register(&mut self, name: TempId, ty: Type) {
        self.variables.insert(name, ty);
    }

    /// Check if a variable is registered
    pub fn contains(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }

    /// Iterate over all variables (name, type)
    pub fn iter(&self) -> impl Iterator<Item = (&TempId, &Type)> {
        self.variables.iter()
    }

    /// Check if a name is a temp variable (starts with '$')
    pub fn is_temp(name: &str) -> bool {
        name.starts_with('$')
    }
}

/// Context for type resolution - provides access to function signatures and struct definitions
pub struct TypeContext<'a> {
    /// Variable types
    pub vars: &'a VariableRegistry,
    /// Function signatures by ID
    pub functions: &'a BTreeMap<FunctionID, FunctionSignature>,
    /// Struct definitions by ID
    pub structs: &'a BTreeMap<StructID, Struct>,
}

impl<'a> TypeContext<'a> {
    pub fn new(
        vars: &'a VariableRegistry,
        functions: &'a BTreeMap<FunctionID, FunctionSignature>,
        structs: &'a BTreeMap<StructID, Struct>,
    ) -> Self {
        Self { vars, functions, structs }
    }

    /// Get function return type
    pub fn function_return_type(&self, id: FunctionID) -> &Type {
        &self.functions.get(&id)
            .unwrap_or_else(|| panic!("Function {} not found in TypeContext", id))
            .return_type
    }

    /// Get struct field type
    pub fn struct_field_type(&self, struct_id: StructID, field_index: usize) -> &Type {
        let s = self.structs.get(&struct_id)
            .unwrap_or_else(|| panic!("Struct {} not found in TypeContext", struct_id));
        &s.fields.get(field_index)
            .unwrap_or_else(|| panic!("Field {} not found in struct {}", field_index, s.name))
            .field_type
    }

    /// Get struct field types as a tuple (for Unpack)
    pub fn struct_fields_tuple(&self, struct_id: StructID) -> Type {
        let s = self.structs.get(&struct_id)
            .unwrap_or_else(|| panic!("Struct {} not found in TypeContext", struct_id));
        Type::Tuple(s.fields.iter().map(|f| f.field_type.clone()).collect())
    }
}
