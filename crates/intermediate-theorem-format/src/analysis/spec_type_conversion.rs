// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Spec type conversion system
//!
//! This pass generates conversion functions for types that have spec representations.
//! For example, I32 (implementation) can have Int (spec) as its spec representation.
//!
//! The system works by:
//! 1. Finding struct types that should have spec representations (e.g., I32, I128)
//! 2. Generating conversion functions (axioms) that user can later prove
//! 3. Registering these conversions in the Program's ConversionRegistry

use crate::data::conversion::TypeSpec;
use crate::{FunctionID, Program, Type};

/// Generate conversion functions for types that need spec representations
pub fn generate_spec_type_conversions(program: &mut Program) {
    // Register int_ops conversion functions that already exist
    // These are native functions from the int_ops module
    register_int_ops_conversions(program);
}

/// Register int_ops conversion functions in the conversion registry
fn register_int_ops_conversions(program: &mut Program) {
    // Find the int_ops module functions
    let int_ops_functions: Vec<(String, usize, usize)> = program
        .functions
        .iter_base()
        .filter_map(|(base_id, func)| {
            let module = program.modules.get(func.module_id);
            // Check if this is from int_ops module
            if module.name.ends_with("int_ops") {
                eprintln!("[CONV_REG] Found int_ops function: {}", func.name);
                Some((func.name.clone(), base_id, func.module_id))
            } else {
                None
            }
        })
        .collect();

    eprintln!(
        "[CONV_REG] Found {} int_ops functions total",
        int_ops_functions.len()
    );

    // Find I32 and I128 struct types
    let int_structs: Vec<(usize, String)> = program
        .structs
        .items
        .iter()
        .filter_map(|(struct_id, struct_def)| {
            let struct_name = &struct_def.name;
            if struct_name == "I32" || struct_name == "I128" {
                Some((*struct_id, struct_name.clone()))
            } else {
                None
            }
        })
        .collect();

    // Register conversions for each integer struct
    for (struct_id, struct_name) in int_structs {
        let impl_type = Type::Struct {
            struct_id,
            type_args: vec![],
        };

        // The spec type is unbounded Int (SInt(0))
        let spec_type = Type::SInt(0);

        // Find the conversion functions from int_ops
        let to_spec_name = format!("{}_to_int", struct_name.to_lowercase());
        let from_spec_name = format!("int_to_{}", struct_name.to_lowercase());

        let to_spec_fn = int_ops_functions
            .iter()
            .find(|(name, _, _)| name == &to_spec_name)
            .map(|(_, base_id, _)| FunctionID::new(*base_id));

        let from_spec_fn = int_ops_functions
            .iter()
            .find(|(name, _, _)| name == &from_spec_name)
            .map(|(_, base_id, _)| FunctionID::new(*base_id));

        // Register if to_spec_fn exists (from_spec_fn is optional - we may not need it)
        // For goal generation, we only need to convert FROM impl types TO spec types
        if let Some(to_spec_fn) = to_spec_fn {
            eprintln!(
                "[CONV_REG] Registering conversion for {} -> Int",
                struct_name
            );
            // Use to_spec_fn as a placeholder for from_spec if not available
            // (we don't use from_spec_fn in goal generation anyway)
            let from_spec_fn = from_spec_fn.unwrap_or(to_spec_fn);
            program.conversions.register(
                impl_type,
                TypeSpec {
                    spec_type,
                    to_spec_fn,
                    from_spec_fn,
                },
            );
        } else {
            eprintln!("[CONV_REG] WARNING: Could not find to_spec conversion function for {}: to_spec={:?} from_spec={:?}",
                struct_name, to_spec_fn.is_some(), from_spec_fn.is_some());
        }
    }
}
