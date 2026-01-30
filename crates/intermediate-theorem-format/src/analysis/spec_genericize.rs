// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Makes spec functions generic by inferring typeclass constraints.
//!
//! This pass analyzes spec functions and:
//! 1. Identifies concrete integer/numeric types (I32, U128, etc.)
//! 2. Replaces them with type parameters (I, U)
//! 3. Infers required typeclasses based on operations used
//! 4. Stores the transformation metadata for the renderer

use crate::data::functions::Function;
use crate::data::Program;
use crate::{FunctionID, IRNode, Type};
use std::collections::{HashMap, HashSet};

/// Metadata about how a spec function should be generified
#[derive(Debug, Clone)]
pub struct GenericSpec {
    /// Type parameters to add: name -> original concrete type
    pub type_params: HashMap<String, Type>,
    /// Typeclass constraints for each type parameter
    pub constraints: HashMap<String, HashSet<TypeClass>>,
    /// Mapping from old variable names to new types (for IR rewriting)
    pub type_substitutions: HashMap<String, String>,
}

/// Typeclasses available in the Lean prelude
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeClass {
    IntegerType,
    NumericType,
    BitwiseNumeric,
    HasRealPow,
}

impl TypeClass {
    pub fn lean_name(&self) -> &'static str {
        match self {
            TypeClass::IntegerType => "IntegerType",
            TypeClass::NumericType => "NumericType",
            TypeClass::BitwiseNumeric => "BitwiseNumeric",
            TypeClass::HasRealPow => "HasRealPow",
        }
    }
}

/// Generate generic spec metadata for all spec functions
pub fn analyze_spec_generics(program: &Program) -> HashMap<FunctionID, GenericSpec> {
    let mut generics = HashMap::new();

    // Process all spec functions (runtime variants only)
    for (func_id, func) in program.functions.iter() {
        if func_id.is_runtime() && func.is_spec() {
            if let Some(spec) = analyze_function_generics(func) {
                generics.insert(func_id, spec);
            }
        }
    }

    generics
}

/// Analyze a single function to determine generic parameters and constraints
fn analyze_function_generics(func: &Function) -> Option<GenericSpec> {
    let mut type_params = HashMap::new();
    let mut constraints: HashMap<String, HashSet<TypeClass>> = HashMap::new();
    let mut type_substitutions = HashMap::new();

    // Step 1: Find all concrete integer/numeric types in parameters and return type
    let mut param_types_to_genericize = Vec::new();

    for param in &func.signature.parameters {
        if let Some((type_param_name, type_class)) = get_generic_mapping(&param.param_type) {
            param_types_to_genericize.push((
                param.name.clone(),
                type_param_name.clone(),
                param.param_type.clone(),
            ));
            type_params
                .entry(type_param_name.clone())
                .or_insert(param.param_type.clone());
            constraints
                .entry(type_param_name)
                .or_default()
                .insert(type_class);
        }
    }

    // Check return type
    if let Some((type_param_name, type_class)) = get_generic_mapping(&func.signature.return_type) {
        type_params
            .entry(type_param_name.clone())
            .or_insert(func.signature.return_type.clone());
        constraints
            .entry(type_param_name)
            .or_default()
            .insert(type_class);
    }

    // If no types to genericize, skip
    if type_params.is_empty() {
        return None;
    }

    // Step 2: Analyze function body to infer additional constraints
    infer_constraints_from_body(&func.body, &type_params, &mut constraints);

    // Step 3: Build substitution map (parameter names -> type parameter names)
    for (param_name, type_param_name, _) in param_types_to_genericize {
        type_substitutions.insert(param_name, type_param_name);
    }

    Some(GenericSpec {
        type_params,
        constraints,
        type_substitutions,
    })
}

/// Map a concrete type to its generic type parameter name and base typeclass
fn get_generic_mapping(ty: &Type) -> Option<(String, TypeClass)> {
    match ty {
        // Signed integers -> IntegerType I
        Type::SInt(8)
        | Type::SInt(16)
        | Type::SInt(32)
        | Type::SInt(64)
        | Type::SInt(128)
        | Type::SInt(256) => Some(("I".to_string(), TypeClass::IntegerType)),
        // Unsigned integers -> NumericType U
        Type::UInt(8)
        | Type::UInt(16)
        | Type::UInt(32)
        | Type::UInt(64)
        | Type::UInt(128)
        | Type::UInt(256) => Some(("U".to_string(), TypeClass::NumericType)),
        _ => None,
    }
}

/// Infer additional typeclass constraints by analyzing operations in the function body.
/// Uses iter() to traverse all nodes and find bitwise operations that require BitwiseNumeric.
fn infer_constraints_from_body(
    node: &IRNode,
    type_params: &HashMap<String, Type>,
    constraints: &mut HashMap<String, HashSet<TypeClass>>,
) {
    use crate::BinOp;

    // Check if any node in the tree contains bitwise operations
    let has_bitwise_ops = node.iter().any(|n| {
        matches!(
            n,
            IRNode::BinOp {
                op: BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr,
                ..
            }
        )
    });

    // If bitwise operations are present, all type params need BitwiseNumeric
    if has_bitwise_ops {
        for type_param in type_params.keys() {
            constraints
                .entry(type_param.clone())
                .or_default()
                .insert(TypeClass::BitwiseNumeric);
        }
    }
}

/// Main entry point: Analyze all spec functions and generate generic metadata
pub fn genericize_specs(program: &mut Program) {
    let generics = analyze_spec_generics(program);
    program.generic_specs = generics;
}
