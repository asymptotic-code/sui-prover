// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders complete TheoremProgram to Lean files.

use super::function_renderer::render_function;
use super::lean_writer::LeanWriter;
use super::struct_renderer::render_struct;
use crate::escape;
use intermediate_theorem_format::{FunctionID, FunctionVariant, Program};
use std::collections::HashSet;
use std::fs;
use std::path::Path;

/// Render program to directory structure (organized by module hierarchy).
/// output_dir should be the Impls/ directory (e.g., output/Impls)
/// Specs will be written to the sibling Specs/ directory (e.g., output/Specs)
pub fn render_to_directory(
    program: &Program,
    output_dir: &Path,
    prelude_imports: &[String],
) -> anyhow::Result<()> {
    fs::create_dir_all(output_dir)?;

    copy_native_packages(program, output_dir)?;

    for (&module_id, module) in &program.modules {
        let mut module_output = String::new();

        module_output.push_str(&format!("-- Module: {}\n\n", module.name));

        // Prelude imports
        for prelude_import in prelude_imports {
            module_output.push_str(&format!("import {}\n", prelude_import));
        }

        // Module imports
        for &required_module_id in &module.required_imports {
            let required_module = program.modules.get(required_module_id);
            let namespace = escape::module_name_to_namespace(&required_module.name);
            module_output.push_str(&format!(
                "import Impls.{}.{}\n",
                required_module.package_name, namespace
            ));
        }

        // Native imports
        let has_native_functions = program
            .functions
            .values()
            .any(|f| f.module_id == module_id && f.is_native());
        if has_native_functions {
            let namespace_name = escape::module_name_to_namespace(&module.name);
            let natives_path = output_dir
                .join(&module.package_name)
                .join(format!("{}Natives.lean", namespace_name));
            if natives_path.exists() {
                module_output.push_str(&format!(
                    "import Impls.{}.{}Natives\n",
                    module.package_name, namespace_name
                ));
            }
        }

        module_output.push('\n');

        let namespace_name = escape::module_name_to_namespace(&module.name);
        module_output.push_str(&format!("namespace {}\n\n", namespace_name));

        // Structs
        for (_, struct_def) in &program.structs {
            if struct_def.module_id == module_id {
                let mut writer = LeanWriter::new(String::new());
                render_struct(struct_def, program, &namespace_name, &mut writer);
                module_output.push_str(&writer.into_inner());
            }
        }

        // Functions - iterate by base function to maintain dependency order
        // For each base function, render it and all its non-spec variants together
        for base_id in program.functions.iter_base_ids() {
            let base_func = program.functions.get(&FunctionID::new(base_id));
            if base_func.module_id != module_id {
                continue;
            }
            if base_func.is_native() {
                continue;
            }

            // Render the base (runtime) function only if it's not monadic
            // Monadic runtime functions are skipped - we only need .pure and .aborts variants for verification
            let base_func_id = FunctionID::new(base_id);
            if !base_func.is_monadic() {
                let writer = LeanWriter::new(String::new());
                let writer =
                    render_function(base_func_id, base_func, program, &namespace_name, writer);
                let rendered = writer.into_inner();
                if !rendered.trim().is_empty() {
                    module_output.push_str(&rendered);
                    module_output.push('\n');
                }
            }

            // Then render non-spec variants (Pure, Aborts) for this base function
            for (variant_id, variant_func) in program.functions.variants_for(base_id) {
                // Skip spec-derived variants (requires, ensures) - they go in Specs/ folder
                if variant_id.variant.is_spec_variant() {
                    continue;
                }

                let writer = LeanWriter::new(String::new());
                let writer =
                    render_function(variant_id, variant_func, program, &namespace_name, writer);
                let rendered = writer.into_inner();
                if !rendered.trim().is_empty() {
                    module_output.push_str(&rendered);
                    module_output.push('\n');
                }
            }
        }

        // Ensure blank line before closing namespace
        if !module_output.ends_with("\n\n") && !module_output.ends_with("namespace") {
            module_output.push('\n');
        }

        module_output.push_str(&format!("end {}\n", namespace_name));

        // Write module file
        let module_path = format!("{}/{}.lean", module.package_name, namespace_name);
        let module_file = output_dir.join(&module_path);

        if let Some(parent) = module_file.parent() {
            fs::create_dir_all(parent)?;
        }

        fs::write(module_file, module_output)?;
    }

    // Render spec functions to Specs/ folder
    render_spec_files(program, output_dir, prelude_imports)?;

    Ok(())
}

/// Render spec functions (.requires and .ensures) to Specs/ folder
fn render_spec_files(
    program: &Program,
    impls_dir: &Path,
    prelude_imports: &[String],
) -> anyhow::Result<()> {
    // Specs directory is sibling to Impls
    let specs_dir = impls_dir.parent().unwrap().join("Specs");
    fs::create_dir_all(&specs_dir)?;

    // Group spec functions by base function name and module
    let mut spec_functions_by_base: std::collections::HashMap<
        (usize, String),
        Vec<(FunctionID, &intermediate_theorem_format::Function)>,
    > = std::collections::HashMap::new();

    for (func_id, func) in program.functions.iter() {
        // Check if this is a spec-derived variant
        if func_id.variant.is_spec_variant() {
            spec_functions_by_base
                .entry((func.module_id, func.name.clone()))
                .or_default()
                .push((func_id, func));
        }
    }

    // Render each group to a separate file
    for ((module_id, base_name), funcs) in spec_functions_by_base {
        let module = program.modules.get(module_id);
        let namespace_name = escape::module_name_to_namespace(&module.name);

        let mut spec_output = String::new();
        spec_output.push_str(&format!("-- Spec for function: {}\n\n", base_name));

        // Prelude imports
        for prelude_import in prelude_imports {
            spec_output.push_str(&format!("import {}\n", prelude_import));
        }

        // Import the implementation module
        spec_output.push_str(&format!(
            "import Impls.{}.{}\n",
            module.package_name, namespace_name
        ));

        spec_output.push('\n');
        spec_output.push_str(&format!("namespace {}\n\n", namespace_name));

        // Collect requires and ensures function names for theorem generation
        let mut ensures_names: Vec<String> = Vec::new();
        let mut requires_func: Option<&intermediate_theorem_format::Function> = None;
        let mut first_ensures_func: Option<&intermediate_theorem_format::Function> = None;

        // Render each spec function
        for (func_id, func) in &funcs {
            let writer = LeanWriter::new(String::new());
            let writer = render_function(*func_id, func, program, &namespace_name, writer);
            let rendered = writer.into_inner();

            if !rendered.trim().is_empty() {
                spec_output.push_str(&rendered);
                spec_output.push('\n');
            }

            // Track requires/ensures for theorem generation
            match func_id.variant {
                FunctionVariant::Requires => {
                    requires_func = Some(*func);
                }
                FunctionVariant::Ensures(_) => {
                    ensures_names.push(escape::escape_identifier(&func.full_name(func_id.variant)));
                    if first_ensures_func.is_none() {
                        first_ensures_func = Some(*func);
                    }
                }
                _ => {}
            }
        }

        // Generate the verification theorem
        // Use requires function signature if available, otherwise use first ensures function
        if !ensures_names.is_empty() {
            let signature_func = requires_func.or(first_ensures_func);
            if let Some(sig_func) = signature_func {
                spec_output.push_str(&generate_verification_theorem(
                    &base_name,
                    &sig_func.signature,
                    requires_func.is_some(),
                    &ensures_names,
                    program,
                ));
                spec_output.push('\n');
            }
        }

        spec_output.push_str(&format!("end {}\n", namespace_name));

        // Write to Specs/<package>/<base_name>.lean
        let spec_file = specs_dir
            .join(&module.package_name)
            .join(format!("{}.lean", base_name));

        if let Some(parent) = spec_file.parent() {
            fs::create_dir_all(parent)?;
        }

        fs::write(spec_file, spec_output)?;
    }

    Ok(())
}

/// Generate a verification theorem for a spec function
/// The theorem states: requires → ensures_0 ∧ ensures_1 ∧ ...
/// If has_requires is false, the theorem is just: ensures_0 ∧ ensures_1 ∧ ...
fn generate_verification_theorem(
    base_name: &str,
    signature: &intermediate_theorem_format::FunctionSignature,
    has_requires: bool,
    ensures_names: &[String],
    program: &Program,
) -> String {
    use crate::renderer::type_renderer::type_to_string;

    let escaped_base = escape::escape_identifier(base_name);
    let mut output = String::new();

    // Build type parameter list (e.g., "(tv0 : Type) [BEq tv0] [Inhabited tv0]")
    let type_param_decls: Vec<String> = signature
        .type_params
        .iter()
        .map(|tp| format!("({} : Type) [BEq {}] [Inhabited {}]", tp, tp, tp))
        .collect();

    // Build parameter list for the theorem
    let param_decls: Vec<String> = signature
        .parameters
        .iter()
        .map(|p| {
            let name = escape::escape_identifier(&p.name);
            let ty = type_to_string(&p.param_type, program, None);
            format!("({} : {})", name, ty)
        })
        .collect();

    // Combine type params and regular params
    let all_decls: Vec<String> = type_param_decls.into_iter().chain(param_decls).collect();

    let param_list = if all_decls.is_empty() {
        String::new()
    } else {
        format!(" {}", all_decls.join(" "))
    };

    // Build argument list for function calls (just the names)
    let type_param_names: Vec<String> = signature.type_params.clone();
    let param_names: Vec<String> = signature
        .parameters
        .iter()
        .map(|p| escape::escape_identifier(&p.name))
        .collect();

    let all_args: Vec<String> = type_param_names.into_iter().chain(param_names).collect();

    let args_str = all_args.join(" ");

    // Build the ensures conjunction
    let ensures_calls: Vec<String> = ensures_names
        .iter()
        .map(|name| {
            if args_str.is_empty() {
                name.clone()
            } else {
                format!("{} {}", name, args_str)
            }
        })
        .collect();

    let ensures_conjunction = if ensures_calls.len() == 1 {
        ensures_calls[0].clone()
    } else {
        ensures_calls.join(" ∧\n    ")
    };

    // Generate the theorem
    output.push_str(&format!(
        "theorem {}.verified{} :\n",
        escaped_base, param_list
    ));

    if has_requires {
        // Build the requires call
        let requires_call = if args_str.is_empty() {
            format!("{}.requires", escaped_base)
        } else {
            format!("{}.requires {}", escaped_base, args_str)
        };
        output.push_str(&format!("  {} →\n", requires_call));
        output.push_str(&format!("    {} := by\n", ensures_conjunction));
    } else {
        // No requires, just the ensures conjunction
        output.push_str(&format!("    {} := by\n", ensures_conjunction));
    }
    output.push_str("  sorry\n");

    output
}

/// Copy native package implementations from lemmas directory.
fn copy_native_packages(program: &Program, output_dir: &Path) -> anyhow::Result<()> {
    let lemmas_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
    let mut copied_modules = HashSet::new();

    for (module_id, module) in program.modules.iter() {
        let has_native_functions = program
            .functions
            .values()
            .any(|f| f.module_id == *module_id && f.is_native());

        if !has_native_functions {
            continue;
        }

        let module_key = format!("{}::{}", module.package_name, module.name);
        if copied_modules.contains(&module_key) {
            continue;
        }

        let lemma_file = format!(
            "natives/{}/{}.lean",
            module.package_name,
            escape::capitalize_first(&module.name)
        );
        let source_path = lemmas_dir.join(&lemma_file);

        if !source_path.exists() {
            continue;
        }

        let namespace = escape::module_name_to_namespace(&module.name);
        let dest_path = output_dir
            .join(&module.package_name)
            .join(format!("{}Natives.lean", namespace));

        if let Some(parent) = dest_path.parent() {
            fs::create_dir_all(parent)?;
        }

        fs::copy(&source_path, &dest_path)?;
        copied_modules.insert(module_key);
    }

    Ok(())
}
