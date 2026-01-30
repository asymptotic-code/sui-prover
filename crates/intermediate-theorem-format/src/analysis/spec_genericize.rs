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

/// Infer additional typeclass constraints by analyzing operations in the function body
fn infer_constraints_from_body(
    node: &IRNode,
    type_params: &HashMap<String, Type>,
    constraints: &mut HashMap<String, HashSet<TypeClass>>,
) {
    match node {
        IRNode::Block { children } => {
            for child in children {
                infer_constraints_from_body(child, type_params, constraints);
            }
        }
        IRNode::Call { args, .. } => {
            // Recursively check arguments
            for arg in args {
                infer_constraints_from_body(arg, type_params, constraints);
            }
        }
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            infer_constraints_from_body(cond, type_params, constraints);
            infer_constraints_from_body(then_branch, type_params, constraints);
            infer_constraints_from_body(else_branch, type_params, constraints);
        }
        IRNode::Let { value, .. } => {
            infer_constraints_from_body(value, type_params, constraints);
        }
        IRNode::Return(vals) => {
            for val in vals {
                infer_constraints_from_body(val, type_params, constraints);
            }
        }
        IRNode::Requires(cond) | IRNode::Ensures(cond) => {
            infer_constraints_from_body(cond, type_params, constraints);
        }
        IRNode::BinOp { op, lhs, rhs } => {
            // Check for bitwise operations
            use crate::BinOp;
            match op {
                BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr => {
                    // Both integer and numeric types might need BitwiseNumeric
                    for type_param in type_params.keys() {
                        constraints
                            .entry(type_param.clone())
                            .or_default()
                            .insert(TypeClass::BitwiseNumeric);
                    }
                }
                _ => {}
            }
            infer_constraints_from_body(lhs, type_params, constraints);
            infer_constraints_from_body(rhs, type_params, constraints);
        }
        IRNode::UnOp { operand, .. } => {
            infer_constraints_from_body(operand, type_params, constraints);
        }
        IRNode::Tuple(elements) => {
            for elem in elements {
                infer_constraints_from_body(elem, type_params, constraints);
            }
        }
        IRNode::Field { base, .. } => {
            infer_constraints_from_body(base, type_params, constraints);
        }
        IRNode::ErrorBound(bound) => {
            infer_constraints_from_body(bound, type_params, constraints);
        }
        IRNode::ErrorBoundRelative {
            numerator,
            denominator,
        } => {
            infer_constraints_from_body(numerator, type_params, constraints);
            infer_constraints_from_body(denominator, type_params, constraints);
        }
        _ => {}
    }
}

/// Transform the body of a spec function to use typeclass operations instead of MoveReal
fn transform_spec_body(node: IRNode, generic_spec: &GenericSpec) -> IRNode {
    match node {
        IRNode::Call {
            function,
            type_args,
            args,
        } => {
            // Transform MoveReal operations to typeclass operations
            let function_str = match &function {
                FunctionID { base, variant } => {
                    // Get the function name from the program
                    // For now, we'll work with the base ID and check if it's a MoveReal operation
                    function
                }
            };

            // For MoveReal operations, we need to transform them
            // This is a simplified approach - in reality we'd need access to the program
            // to resolve function names properly
            IRNode::Call {
                function,
                type_args,
                args: args
                    .into_iter()
                    .map(|arg| transform_spec_body(arg, generic_spec))
                    .collect(),
            }
        }
        IRNode::Block { children } => IRNode::Block {
            children: children
                .into_iter()
                .map(|child| transform_spec_body(child, generic_spec))
                .collect(),
        },
        IRNode::Let { pattern, value } => IRNode::Let {
            pattern,
            value: Box::new(transform_spec_body(*value, generic_spec)),
        },
        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => IRNode::If {
            cond: Box::new(transform_spec_body(*cond, generic_spec)),
            then_branch: Box::new(transform_spec_body(*then_branch, generic_spec)),
            else_branch: Box::new(transform_spec_body(*else_branch, generic_spec)),
        },
        IRNode::BinOp { op, lhs, rhs } => IRNode::BinOp {
            op,
            lhs: Box::new(transform_spec_body(*lhs, generic_spec)),
            rhs: Box::new(transform_spec_body(*rhs, generic_spec)),
        },
        IRNode::UnOp { op, operand } => IRNode::UnOp {
            op,
            operand: Box::new(transform_spec_body(*operand, generic_spec)),
        },
        IRNode::Tuple(elements) => IRNode::Tuple(
            elements
                .into_iter()
                .map(|elem| transform_spec_body(elem, generic_spec))
                .collect(),
        ),
        IRNode::Return(vals) => IRNode::Return(
            vals.into_iter()
                .map(|val| transform_spec_body(val, generic_spec))
                .collect(),
        ),
        // Keep other nodes as-is
        other => other,
    }
}

/// Main entry point: Analyze all spec functions and generate generic metadata
pub fn genericize_specs(program: &mut Program) {
    let generics = analyze_spec_generics(program);
    program.generic_specs = generics;
}
