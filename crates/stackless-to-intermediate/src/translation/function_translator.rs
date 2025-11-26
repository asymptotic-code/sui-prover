// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translates a single Move function to TheoremIR
//!
//! Single responsibility: Translate one function body.
//! Populates SSA registry with type information from FunctionTarget.

use crate::control_flow_reconstruction::reconstruct_and_translate;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::TempId;
use intermediate_theorem_format::{Parameter, Statement, VariableRegistry};
use move_stackless_bytecode::function_target::FunctionTarget;

/// Translate a single function body
/// Returns the translated statement and populates the registry
pub fn translate_function<'a, 'b, 'c>(
    builder: &'a mut ProgramBuilder<'b>,
    target: &'a FunctionTarget<'c>,
    registry: &'a mut VariableRegistry,
    parameters: &[Parameter],
) -> Statement {
    let code = target.get_bytecode();

    // Native function
    if code.is_empty() {
        return Statement::Sequence(vec![]);
    }

    // Populate SSA registry with types and set parameter names
    populate_types(builder, target, registry, parameters);

    // Use integrated control flow reconstruction and bytecode translation
    reconstruct_and_translate(
        builder,
        target,
        code,
        registry,
    )
}

/// Populate SSA registry with type information from FunctionTarget
fn populate_types(
    builder: &mut ProgramBuilder,
    target: &FunctionTarget,
    registry: &mut VariableRegistry,
    parameters: &[Parameter],
) {
    let local_count = target.get_local_count();
    let param_count = target.get_parameter_count();

    for local_idx in 0..local_count {
        let temp_id = local_idx as TempId;

        // Skip if already registered
        if registry.has_bytecode_temp(temp_id) {
            continue;
        }

        let move_type = target.get_local_type(local_idx);
        let theorem_type = builder.convert_type(move_type);

        // Get the name from FunctionTarget
        let symbol = target.get_local_name(local_idx);
        let compiler_name = symbol.display(builder.env().symbol_pool()).to_string();

        // Determine name: for parameters, use the human-readable name from the signature
        // For other locals, use the compiler-generated name from FunctionTarget
        let mut name = if local_idx < param_count {
            parameters.get(local_idx)
                .map(|p| p.name.clone())
                .unwrap_or_else(|| compiler_name.clone())
        } else {
            compiler_name
        };

        // Sanitize name for Lean: replace invalid characters
        // Lean identifiers can only contain: a-z A-Z 0-9 _ '
        // Move uses: $ # in compiler-generated names
        name = name
            .replace('$', "_")
            .replace('#', "_")
            .replace('.', "_");

        // Remove leading underscore if the name starts with one after sanitization
        if name.starts_with('_') && name.len() > 1 {
            name = name[1..].to_string();
        }

        // Register bytecode temp with all metadata at once
        registry.register_bytecode_temp(temp_id, name, theorem_type);
    }
}
