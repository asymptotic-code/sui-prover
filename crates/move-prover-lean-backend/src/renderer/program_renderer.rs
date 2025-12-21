// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders complete TheoremProgram to Lean files.

use super::function_renderer::render_function;
use super::lean_writer::LeanWriter;
use super::struct_renderer::render_struct;
use crate::escape;
use intermediate_theorem_format::{Function, FunctionID, FunctionVariant, Program};
use std::collections::HashSet;
use std::fmt::Write;
use std::fs;
use std::path::Path;

/// Extract the namespace declared in a native file.
/// Looks for "namespace Foo" declaration.
fn extract_native_namespace(native_file_path: &Path) -> Option<String> {
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("namespace ") {
                if let Some(name) = rest.split_whitespace().next() {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}

/// Extract function names defined in a native file.
/// Looks for patterns like "def foo" or "def foo.pure" etc.
fn extract_native_function_names(native_file_path: &Path) -> HashSet<String> {
    let mut names = HashSet::new();
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let line = line.trim();
            // Match patterns like "def foo", "partial def foo", "def foo.pure", etc.
            if let Some(rest) = line.strip_prefix("def ").or_else(|| line.strip_prefix("partial def ")) {
                // Extract the function name (up to first space or open paren)
                if let Some(name_end) = rest.find(|c: char| c == ' ' || c == '(' || c == ':') {
                    let name = &rest[..name_end];
                    // Also handle names with variants like "foo.pure" -> add "foo"
                    if let Some(base_name) = name.split('.').next() {
                        names.insert(base_name.to_string());
                    }
                    names.insert(name.to_string());
                }
            }
        }
    }
    names
}

/// Extract struct/type names defined in a native file.
/// Looks for patterns like "structure Foo", "abbrev Foo", or exported struct names.
fn extract_native_struct_names(native_file_path: &Path) -> HashSet<String> {
    let mut names = HashSet::new();
    if let Ok(content) = fs::read_to_string(native_file_path) {
        for line in content.lines() {
            let line = line.trim();
            // Match patterns like "structure Foo" or "structure Foo.{u}"
            if let Some(rest) = line.strip_prefix("structure ") {
                // Extract the struct name (up to first space, brace, or where keyword)
                if let Some(name_end) = rest.find(|c: char| c == ' ' || c == '.' || c == '{') {
                    let name = &rest[..name_end];
                    names.insert(name.to_string());
                } else if !rest.is_empty() {
                    // No delimiter found, take the whole thing
                    names.insert(rest.to_string());
                }
            }
            // Match patterns like "abbrev Foo" (type aliases)
            if let Some(rest) = line.strip_prefix("abbrev ") {
                if let Some(name_end) = rest.find(|c: char| c == ' ' || c == ':' || c == '{') {
                    let name = &rest[..name_end];
                    names.insert(name.to_string());
                } else if !rest.is_empty() {
                    names.insert(rest.to_string());
                }
            }
            // Also check for "export ... (Foo ...)" patterns that re-export structs
            if let Some(rest) = line.strip_prefix("export ") {
                // Look for parenthesized list
                if let Some(paren_start) = rest.find('(') {
                    if let Some(paren_end) = rest.find(')') {
                        let exports = &rest[paren_start + 1..paren_end];
                        // First word after ( is often the struct type name
                        for export_name in exports.split_whitespace() {
                            // Struct names typically start with uppercase
                            if export_name.chars().next().map_or(false, |c| c.is_uppercase()) {
                                names.insert(export_name.to_string());
                            }
                        }
                    }
                }
            }
        }
    }
    names
}

/// Render program to directory structure (organized by module hierarchy).
/// output_dir should be the Impls/ directory (e.g., output/Impls)
/// Specs will be written to the sibling Specs/ directory (e.g., output/Specs)
/// project_dir is the project root directory where Proofs/ may exist
pub fn render_to_directory(
    program: &Program,
    output_dir: &Path,
    prelude_imports: &[String],
    project_dir: &Path,
) -> anyhow::Result<()> {
    fs::create_dir_all(output_dir)?;

    let proofs_dir = project_dir.join("Proofs");

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

        let namespace_name = escape::module_name_to_namespace(&module.name);

        // Native imports - check if a natives file exists for this module
        let natives_path = output_dir
            .join(&module.package_name)
            .join(format!("{}Natives.lean", namespace_name));

        // Extract function and struct names from natives file to skip generating them
        let (native_function_names, native_struct_names, native_namespace) = if natives_path.exists() {
            module_output.push_str(&format!(
                "import Impls.{}.{}Natives\n",
                module.package_name, namespace_name
            ));

            // Extract the namespace from the natives file
            let native_ns = extract_native_namespace(&natives_path);

            (
                extract_native_function_names(&natives_path),
                extract_native_struct_names(&natives_path),
                native_ns,
            )
        } else {
            (HashSet::new(), HashSet::new(), None)
        };

        module_output.push('\n');
        module_output.push_str(&format!("namespace {}\n", namespace_name));

        // If the natives file has a different namespace, open it and create re-exports
        let needs_reexports = if let Some(ref ns) = native_namespace {
            if ns != &namespace_name {
                module_output.push_str(&format!("open {}\n", ns));
                true
            } else {
                false
            }
        } else {
            false
        };
        module_output.push('\n');

        // Re-export native functions from the different namespace so they can be called as Module.function
        if needs_reexports {
            if let Some(ref ns) = native_namespace {
                for func_name in &native_function_names {
                    // Create an alias: noncomputable abbrev function_name := NativeNamespace.function_name
                    // Native functions are noncomputable since they depend on Real operations
                    module_output.push_str(&format!("noncomputable abbrev {} := {}.{}\n", func_name, ns, func_name));
                }
                if !native_function_names.is_empty() {
                    module_output.push('\n');
                }
            }
        }

        // Structs - skip those defined in natives file
        for (_, struct_def) in &program.structs {
            if struct_def.module_id == module_id {
                // Skip structs that are defined in the natives file
                if native_struct_names.contains(&struct_def.name) {
                    continue;
                }
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

            // Skip functions that are defined in the natives file
            if native_function_names.contains(&base_func.name) {
                continue;
            }

            // Check if this function's body was replaced by a spec
            // If so, we need to render both the _impl (original) and the spec version (clean)
            let has_original_body = base_func.original_body.is_some();

            if has_original_body {
                // This is a spec-target function - render both _impl and clean spec version

                // 1. Render _impl with original_body
                // Use Pure variant's body (which has aborts stripped) if original has aborts
                let impl_body = if base_func.original_body.as_ref().unwrap().aborts() {
                    // Original has aborts - use Pure variant's body
                    let pure_id = FunctionID::with_variant(base_id, FunctionVariant::Pure);
                    if let Some(pure_func) = program.functions.try_get(&pure_id) {
                        &pure_func.body
                    } else {
                        // Fallback to original if Pure doesn't exist (shouldn't happen)
                        base_func.original_body.as_ref().unwrap()
                    }
                } else {
                    base_func.original_body.as_ref().unwrap()
                };

                let writer = LeanWriter::new(String::new());
                let writer = super::function_renderer::render_function_with_body(
                    base_id,
                    base_func,
                    impl_body,
                    &format!("{}_impl", base_func.name),
                    program,
                    &namespace_name,
                    writer,
                );
                let rendered = writer.into_inner();
                if !rendered.trim().is_empty() {
                    module_output.push_str(&rendered);
                    module_output.push('\n');
                }

                // 2. Render clean spec version with current body (which is the spec body)
                // This version takes .requires as a precondition argument
                let writer = LeanWriter::new(String::new());
                let writer = super::function_renderer::render_spec_replaced_function(
                    base_id,
                    base_func,
                    program,
                    &namespace_name,
                    writer,
                );
                let rendered = writer.into_inner();
                if !rendered.trim().is_empty() {
                    module_output.push_str(&rendered);
                    module_output.push('\n');
                }

                // 3. Render spec_correct theorem
                let writer = LeanWriter::new(String::new());
                let writer = render_spec_correct_theorem(
                    base_id,
                    base_func,
                    program,
                    &namespace_name,
                    &module.package_name,
                    &proofs_dir,
                    prelude_imports,
                    writer,
                );
                let rendered = writer.into_inner();
                if !rendered.trim().is_empty() {
                    module_output.push_str(&rendered);
                    module_output.push('\n');
                }
            } else {
                // Normal function - render the Pure variant if it exists, otherwise render Runtime
                // Non-monadic functions don't have Pure variants, so we fall back to Runtime
                let pure_id = FunctionID::with_variant(base_id, FunctionVariant::Pure);
                let (func_id_to_render, func_to_render) =
                    if let Some(pure_func) = program.functions.try_get(&pure_id) {
                        (pure_id, pure_func)
                    } else {
                        // No Pure variant (non-monadic function) - render Runtime variant
                        let runtime_id = FunctionID::new(base_id);
                        (runtime_id, base_func)
                    };

                let writer = LeanWriter::new(String::new());
                let writer =
                    render_function(func_id_to_render, func_to_render, program, &namespace_name, writer);
                let rendered = writer.into_inner();
                if !rendered.trim().is_empty() {
                    module_output.push_str(&rendered);
                    module_output.push('\n');
                }
            }

            // Render .aborts variant for all functions (not for spec functions though)
            // Spec functions don't have .aborts since they're pure mathematical definitions
            if !base_func.flags.is_spec() {
                let aborts_id = FunctionID::with_variant(base_id, FunctionVariant::Aborts);
                if let Some(aborts_func) = program.functions.try_get(&aborts_id) {
                    let writer = LeanWriter::new(String::new());
                    let writer = render_function(aborts_id, aborts_func, program, &namespace_name, writer);
                    let rendered = writer.into_inner();
                    if !rendered.trim().is_empty() {
                        module_output.push_str(&rendered);
                        module_output.push('\n');
                    }
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

    // Render spec functions (.requires, .ensures) to Specs/ folder
    render_spec_files(program, output_dir, prelude_imports, project_dir)?;

    // Render spec equivalence theorems to Specs/ folder
    // NOTE: Removed render_spec_equivalence_theorems to avoid duplicate theorem declarations
    // The spec_correct theorems are now only generated in Impls/<package>/<Module>.lean

    // Generate proof obligations for calls to spec-target functions with .requires
    render_requires_proof_obligations(program, output_dir, prelude_imports, project_dir)?;

    Ok(())
}

/// Render spec functions (.requires and .ensures) to SpecDefs/ and Specs/ folders.
///
/// Structure to avoid circular dependencies:
/// - SpecDefs/<package>/<func_name>.lean: Contains .requires and .ensures definitions
/// - Proofs/<package>/<namespace>/<func_name>_proof.lean: Imports SpecDefs, provides proof
/// - Specs/<package>/<func_name>.lean: Imports SpecDefs and Proofs, has the verified theorem
///
/// Dependency chain: SpecDefs <- Proofs <- Specs
fn render_spec_files(
    program: &Program,
    impls_dir: &Path,
    prelude_imports: &[String],
    project_dir: &Path,
) -> anyhow::Result<()> {
    // Directories are siblings to Impls
    let parent_dir = impls_dir.parent().unwrap();
    let spec_defs_dir = parent_dir.join("SpecDefs");
    let specs_dir = parent_dir.join("Specs");
    let proofs_dir = project_dir.join("Proofs");
    fs::create_dir_all(&spec_defs_dir)?;
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

        // Collect requires and ensures function names first to determine signature
        let mut ensures_names: Vec<String> = Vec::new();
        let mut requires_func: Option<&intermediate_theorem_format::Function> = None;
        let mut first_ensures_func: Option<&intermediate_theorem_format::Function> = None;

        for (func_id, func) in &funcs {
            match func_id.variant {
                FunctionVariant::Requires => {
                    requires_func = Some(*func);
                }
                FunctionVariant::Ensures(_) => {
                    if first_ensures_func.is_none() {
                        first_ensures_func = Some(*func);
                    }
                }
                _ => {}
            }
        }

        // Check if a proof exists in the library
        let proof_import = find_proof_in_library(
            &proofs_dir,
            &base_name,
            &module.package_name,
            &namespace_name,
        );

        // Determine ensures_names for template generation
        let mut temp_ensures_names: Vec<String> = Vec::new();
        for (func_id, _func) in &funcs {
            if let FunctionVariant::Ensures(_) = func_id.variant {
                temp_ensures_names.push(escape::escape_identifier(&_func.full_name(func_id.variant)));
            }
        }

        // If no proof exists, generate a template
        if proof_import.is_none() {
            if let Some(sig_func) = requires_func.or(first_ensures_func) {
                let _ = generate_proof_template(
                    &proofs_dir,
                    &base_name,
                    &module.package_name,
                    &namespace_name,
                    &sig_func.signature,
                    program,
                    prelude_imports,
                    false, // is_spec_equivalence
                    &temp_ensures_names,
                    requires_func.is_some(),
                );
            }
        }

        // ========== PART 1: Generate SpecDefs file (definitions only) ==========
        let mut spec_defs_output = String::new();
        spec_defs_output.push_str(&format!("-- Spec definitions for function: {}\n\n", base_name));

        // Prelude imports
        for prelude_import in prelude_imports {
            spec_defs_output.push_str(&format!("import {}\n", prelude_import));
        }

        // Import the implementation module
        spec_defs_output.push_str(&format!(
            "import Impls.{}.{}\n",
            module.package_name, namespace_name
        ));

        spec_defs_output.push('\n');
        spec_defs_output.push_str(&format!("namespace {}\n\n", namespace_name));

        // Re-initialize for rendering
        ensures_names.clear();
        requires_func = None;
        first_ensures_func = None;

        // Render each spec function definition
        for (func_id, func) in &funcs {
            let writer = LeanWriter::new(String::new());
            let writer = render_function(*func_id, func, program, &namespace_name, writer);
            let rendered = writer.into_inner();

            if !rendered.trim().is_empty() {
                spec_defs_output.push_str(&rendered);
                spec_defs_output.push('\n');
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

        spec_defs_output.push_str(&format!("end {}\n", namespace_name));

        // Write to SpecDefs/<package>/<base_name>.lean
        let spec_defs_file = spec_defs_dir
            .join(&module.package_name)
            .join(format!("{}.lean", base_name));

        if let Some(parent) = spec_defs_file.parent() {
            fs::create_dir_all(parent)?;
        }

        fs::write(spec_defs_file, spec_defs_output)?;

        // ========== PART 2: Generate Specs file (imports SpecDefs + Proofs, theorem only) ==========
        let mut spec_output = String::new();
        spec_output.push_str(&format!("-- Spec for function: {}\n\n", base_name));

        // Import SpecDefs (contains the definitions)
        spec_output.push_str(&format!(
            "import SpecDefs.{}.{}\n",
            module.package_name, base_name
        ));

        // Import proof library if it exists
        if let Some(ref proof_path) = proof_import {
            spec_output.push_str(&format!("import {}\n", proof_path));
        }

        spec_output.push('\n');
        spec_output.push_str(&format!("namespace {}\n\n", namespace_name));

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
                    proof_import.as_deref(),
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
    proof_import: Option<&str>,
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

    // Use proof from library if available, otherwise use sorry
    if let Some(proof_ref) = proof_import {
        if args_str.is_empty() {
            output.push_str(&format!("  exact {}.proof\n", proof_ref));
        } else {
            output.push_str(&format!("  exact {}.proof {}\n", proof_ref, args_str));
        }
    } else {
        output.push_str("  sorry\n");
    }

    output
}

/// Check if a proof exists in the Proofs/ directory for a given function.
/// If not, create a template proof file.
fn find_proof_in_library(
    proofs_dir: &Path,
    func_name: &str,
    package_name: &str,
    namespace_name: &str,
) -> Option<String> {
    let proof_file = proofs_dir
        .join(package_name)
        .join(namespace_name)
        .join(format!("{}_proof.lean", func_name));

    if proof_file.exists() {
        Some(format!("Proofs.{}.{}.{}_proof", package_name, namespace_name, func_name))
    } else {
        None
    }
}

/// Generate a proof template file with the correct signature
fn generate_proof_template(
    proofs_dir: &Path,
    func_name: &str,
    package_name: &str,
    namespace_name: &str,
    signature: &intermediate_theorem_format::FunctionSignature,
    program: &Program,
    prelude_imports: &[String],
    is_spec_equivalence: bool,
    ensures_names: &[String],
    has_requires: bool,
) -> anyhow::Result<()> {
    use crate::renderer::type_renderer::type_to_string;

    let proof_file = proofs_dir
        .join(package_name)
        .join(namespace_name)
        .join(format!("{}_proof.lean", func_name));

    // Don't overwrite existing files
    if proof_file.exists() {
        return Ok(());
    }

    // Create directory structure
    if let Some(parent) = proof_file.parent() {
        fs::create_dir_all(parent)?;
    }

    let mut content = String::new();

    // Header comment
    if is_spec_equivalence {
        content.push_str(&format!("-- Proof template for {}\n", func_name));
        content.push_str(&format!("-- This file contains the formal proof that the implementation matches the specification\n"));
    } else {
        content.push_str(&format!("-- Proof template for {} verification\n", func_name));
        content.push_str(&format!("-- This file contains the formal proof for requires/ensures specifications\n"));
    }
    content.push_str(&format!("-- TODO: Complete this proof by replacing 'sorry' with actual proof steps\n\n"));

    // Imports
    for prelude_import in prelude_imports {
        content.push_str(&format!("import {}\n", prelude_import));
    }
    content.push_str(&format!("import Impls.{}.{}\n", package_name, namespace_name));
    // Import the SpecDefs file where .requires and .ensures are defined
    if has_requires || !ensures_names.is_empty() {
        content.push_str(&format!("import SpecDefs.{}.{}\n", package_name, func_name));
    }
    content.push('\n');

    // Namespace
    content.push_str(&format!("namespace Proofs.{}.{}.{}_proof\n\n", package_name, namespace_name, func_name));

    // Build parameter list
    let type_param_decls: Vec<String> = signature
        .type_params
        .iter()
        .map(|tp| format!("({} : Type) [BEq {}] [Inhabited {}]", tp, tp, tp))
        .collect();

    let param_decls: Vec<String> = signature
        .parameters
        .iter()
        .map(|p| {
            let name = escape::escape_identifier(&p.name);
            let ty = type_to_string(&p.param_type, program, None);
            format!("({} : {})", name, ty)
        })
        .collect();

    // Collect Bool params that need Decidable constraints
    let bool_param_constraints: Vec<String> = signature
        .parameters
        .iter()
        .filter(|p| matches!(p.param_type, intermediate_theorem_format::Type::Bool))
        .map(|p| format!("[Decidable {}]", escape::escape_identifier(&p.name)))
        .collect();

    let all_decls: Vec<String> = type_param_decls
        .into_iter()
        .chain(param_decls)
        .chain(bool_param_constraints)
        .collect();

    let param_list = if all_decls.is_empty() {
        String::new()
    } else {
        format!(" {}", all_decls.join(" "))
    };

    // Build argument list
    let type_param_names: Vec<String> = signature.type_params.clone();
    let param_names: Vec<String> = signature
        .parameters
        .iter()
        .map(|p| escape::escape_identifier(&p.name))
        .collect();

    let all_args: Vec<String> = type_param_names.into_iter().chain(param_names).collect();

    let args_str = if all_args.is_empty() {
        String::new()
    } else {
        format!(" {}", all_args.join(" "))
    };

    // Generate theorem based on type
    if is_spec_equivalence {
        content.push_str(&format!("-- Proves that the implementation equals the specification\n"));
        content.push_str(&format!("theorem proof{} :\n", param_list));

        if has_requires {
            let requires_call = if args_str.is_empty() {
                format!("{}.{}.requires", namespace_name, func_name)
            } else {
                format!("{}.{}.requires{}", namespace_name, func_name, args_str)
            };
            content.push_str(&format!("  {} →\n", requires_call));
        }

        content.push_str(&format!("  {}.{}_impl{} = {}.{}{} := by\n",
            namespace_name, func_name, args_str, namespace_name, func_name, args_str));
        content.push_str("  sorry\n\n");
    } else {
        // Build the ensures conjunction with namespace prefix
        let ensures_calls: Vec<String> = ensures_names
            .iter()
            .map(|name| {
                if args_str.is_empty() {
                    format!("{}.{}", namespace_name, name)
                } else {
                    format!("{}.{} {}", namespace_name, name, args_str)
                }
            })
            .collect();

        // If no ensures, the conclusion is True (requires → True)
        let ensures_conjunction = if ensures_calls.is_empty() {
            "True".to_string()
        } else if ensures_calls.len() == 1 {
            ensures_calls[0].clone()
        } else {
            ensures_calls.join(" ∧\n    ")
        };

        content.push_str(&format!("-- Proves the verification conditions\n"));
        content.push_str(&format!("theorem proof{} :\n", param_list));

        if has_requires {
            let requires_call = if args_str.is_empty() {
                format!("{}.{}.requires", namespace_name, func_name)
            } else {
                format!("{}.{}.requires {}", namespace_name, func_name, args_str)
            };
            content.push_str(&format!("  {} →\n", requires_call));
            content.push_str(&format!("    {} := by\n", ensures_conjunction));
        } else {
            content.push_str(&format!("    {} := by\n", ensures_conjunction));
        }
        content.push_str("  sorry\n\n");
    }

    content.push_str(&format!("end Proofs.{}.{}.{}_proof\n", package_name, namespace_name, func_name));

    fs::write(proof_file, content)?;
    Ok(())
}

/// Generate a spec equivalence theorem proving that the _impl version equals the spec version.
/// This is generated when a spec function has a target annotation.
fn generate_spec_equivalence_theorem(
    target_name: &str,
    signature: &intermediate_theorem_format::FunctionSignature,
    program: &Program,
    proof_import: Option<&str>,
    has_requires: bool,
    namespace_name: &str,
) -> String {
    use crate::renderer::type_renderer::type_to_string;

    let escaped_name = escape::escape_identifier(target_name);
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

    let args_str = if all_args.is_empty() {
        String::new()
    } else {
        format!(" {}", all_args.join(" "))
    };

    // Generate the theorem with requires precondition if present
    output.push_str(&format!(
        "theorem {}_spec_correct{} :\n",
        escaped_name, param_list
    ));

    if has_requires {
        // Build the requires call
        let requires_call = if args_str.is_empty() {
            format!("{}.{}.requires", namespace_name, escaped_name)
        } else {
            format!("{}.{}.requires{}", namespace_name, escaped_name, args_str)
        };
        output.push_str(&format!("  {} →\n", requires_call));
    }

    output.push_str(&format!(
        "  {}_impl{} = {}{} := by\n",
        escaped_name, args_str, escaped_name, args_str
    ));

    // Use proof from library if available, otherwise use sorry
    if let Some(proof_ref) = proof_import {
        if args_str.is_empty() {
            output.push_str(&format!("  exact {}.proof\n", proof_ref));
        } else {
            output.push_str(&format!("  exact {}.proof {}\n", proof_ref, args_str));
        }
    } else {
        output.push_str("  sorry\n");
    }

    output
}

/// Render spec equivalence theorems for functions that have spec targets.
/// Creates files in Specs/<package>/<function_name>_spec.lean
fn render_spec_equivalence_theorems(
    program: &Program,
    impls_dir: &Path,
    prelude_imports: &[String],
    project_dir: &Path,
) -> anyhow::Result<()> {
    let specs_dir = impls_dir.parent().unwrap().join("Specs");
    let proofs_dir = project_dir.join("Proofs");
    fs::create_dir_all(&specs_dir)?;

    // Iterate over all spec functions that have a target
    for (spec_base_id, spec_func) in program.functions.iter_base() {
        if let Some(target_base_id) = spec_func.spec_target {
            let target_func = program.functions.get(&FunctionID::new(target_base_id));
            let module = program.modules.get(target_func.module_id);
            let namespace_name = escape::module_name_to_namespace(&module.name);

            // Check if the spec function has a .requires variant
            let requires_id = FunctionID::with_variant(spec_base_id, FunctionVariant::Requires);
            let has_requires = program.functions.try_get(&requires_id).is_some();

            // Check if a proof exists in the library
            let proof_import = find_proof_in_library(
                &proofs_dir,
                &target_func.name,
                &module.package_name,
                &namespace_name,
            );

            // If no proof exists, generate a template
            if proof_import.is_none() {
                let _ = generate_proof_template(
                    &proofs_dir,
                    &target_func.name,
                    &module.package_name,
                    &namespace_name,
                    &target_func.signature,
                    program,
                    prelude_imports,
                    true, // is_spec_equivalence
                    &[], // ensures_names not used for spec equivalence
                    has_requires,
                );
            }

            let mut spec_output = String::new();
            spec_output.push_str(&format!(
                "-- Spec equivalence theorem for {}\n",
                target_func.name
            ));
            spec_output.push_str(&format!(
                "-- Proves that {}_impl = {} (the spec version)\n\n",
                target_func.name, target_func.name
            ));

            // Prelude imports
            for prelude_import in prelude_imports {
                spec_output.push_str(&format!("import {}\n", prelude_import));
            }

            // Import the implementation module (which contains both _impl and spec versions)
            spec_output.push_str(&format!(
                "import Impls.{}.{}\n",
                module.package_name, namespace_name
            ));

            // Import proof library if available
            if let Some(ref proof_path) = proof_import {
                spec_output.push_str(&format!("import {}\n", proof_path));
            }

            spec_output.push('\n');
            spec_output.push_str(&format!("namespace {}\n\n", namespace_name));

            // Generate the equivalence theorem
            spec_output.push_str(&generate_spec_equivalence_theorem(
                &target_func.name,
                &target_func.signature,
                program,
                proof_import.as_deref(),
                has_requires,
                &namespace_name,
            ));

            spec_output.push('\n');
            spec_output.push_str(&format!("end {}\n", namespace_name));

            // Write to Specs/<package>/<target_name>_spec.lean
            let spec_file = specs_dir
                .join(&module.package_name)
                .join(format!("{}_spec.lean", target_func.name));

            if let Some(parent) = spec_file.parent() {
                fs::create_dir_all(parent)?;
            }

            fs::write(spec_file, spec_output)?;
        }
    }

    Ok(())
}

/// Copy native package implementations from lemmas directory.
fn copy_native_packages(program: &Program, output_dir: &Path) -> anyhow::Result<()> {
    let lemmas_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
    let mut copied_modules = HashSet::new();

    // Copy natives for ALL modules (not just those with native functions)
    // This allows us to provide hand-written implementations for functions
    // that the IR generator can't properly translate
    for (_module_id, module) in program.modules.iter() {
        let module_key = format!("{}::{}", module.package_name, module.name);
        if copied_modules.contains(&module_key) {
            continue;
        }

        let capitalized_name = escape::capitalize_first(&module.name);
        let namespace = escape::module_name_to_namespace(&module.name);

        // Try multiple naming conventions for native files:
        // 1. {CapitalizedModuleName}.lean (e.g., Real.lean, Ghost.lean)
        // 2. {CapitalizedModuleName}Natives.lean (e.g., RealNatives.lean)
        // 3. {Namespace}Natives.lean (e.g., MoveRealNatives.lean - for escaped names)
        let possible_files = [
            format!("natives/{}/{}.lean", module.package_name, capitalized_name),
            format!("natives/{}/{}Natives.lean", module.package_name, capitalized_name),
            format!("natives/{}/{}Natives.lean", module.package_name, namespace),
        ];

        let source_path = possible_files
            .iter()
            .map(|f| lemmas_dir.join(f))
            .find(|p| p.exists());

        let source_path = match source_path {
            Some(p) => p,
            None => continue,
        };

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

/// Render a spec_correct theorem for a spec-target function.
/// Always uses `sorry` in Impls to avoid circular dependencies.
/// The Specs files import Proofs and use the actual proofs.
fn render_spec_correct_theorem<W: Write>(
    base_id: usize,
    func: &Function,
    program: &Program,
    namespace_name: &str,
    package_name: &str,
    proofs_dir: &Path,
    prelude_imports: &[String],
    mut w: LeanWriter<W>,
) -> LeanWriter<W> {
    use crate::renderer::type_renderer::type_to_string;

    let escaped_name = escape::escape_identifier(&func.name);

    // Check if there's a .requires function
    let requires_id = FunctionID::with_variant(base_id, FunctionVariant::Requires);
    let has_requires = program.functions.try_get(&requires_id).is_some();

    // Check if a proof exists (for generating templates)
    let proof_exists = find_proof_in_library(
        proofs_dir,
        &func.name,
        package_name,
        namespace_name,
    ).is_some();

    // Generate proof template if none exists
    if !proof_exists {
        let _ = generate_proof_template(
            proofs_dir,
            &func.name,
            package_name,
            namespace_name,
            &func.signature,
            program,
            prelude_imports,
            true, // is_spec_equivalence
            &[],
            has_requires,
        );
    }

    w.write(&format!("-- Spec equivalence theorem for {}\n", func.name));
    w.write(&format!("-- Proves that {}_impl = {} (the spec version)\n", func.name, func.name));
    w.write(&format!("theorem {}_spec_correct", escaped_name));

    // Write type parameters
    if !func.signature.type_params.is_empty() {
        w.write(" ");
        for (i, tp) in func.signature.type_params.iter().enumerate() {
            if i > 0 {
                w.write(" ");
            }
            w.write(&format!("({} : Type) [BEq {}] [Inhabited {}]", tp, tp, tp));
        }
    }

    // Write regular parameters
    for param in &func.signature.parameters {
        w.write(" (");
        w.write(&escape::escape_identifier(&param.name));
        w.write(" : ");
        w.write(&type_to_string(&param.param_type, program, Some(namespace_name)));
        w.write(")");
    }

    // Add [Decidable] constraints for Bool/Prop parameters
    for param in &func.signature.parameters {
        if matches!(param.param_type, intermediate_theorem_format::Type::Bool) {
            w.write(&format!(
                " [Decidable {}]",
                escape::escape_identifier(&param.name)
            ));
        }
    }

    w.write(" :\n  ");

    // Add .requires as hypothesis if it exists
    if has_requires {
        w.write(&escaped_name);
        w.write(".requires");

        // Apply all arguments to .requires
        for param in &func.signature.parameters {
            w.write(" ");
            w.write(&escape::escape_identifier(&param.name));
        }

        w.write(" →\n  ");
    }

    // The conclusion: _impl = clean_spec
    w.write(&escaped_name);
    w.write("_impl");

    // Apply all arguments
    for param in &func.signature.parameters {
        w.write(" ");
        w.write(&escape::escape_identifier(&param.name));
    }

    w.write(" = ");
    w.write(&escaped_name);

    // Apply all arguments (with requires proof if needed)
    for param in &func.signature.parameters {
        w.write(" ");
        w.write(&escape::escape_identifier(&param.name));
    }

    if has_requires {
        w.write(" (by assumption)");
    }

    w.write(" := by\n  ");

    // Always use sorry in Impls - Proofs cannot import Impls without creating a cycle
    // The Specs files import both Impls and Proofs to connect them
    w.write("sorry\n");

    w
}

/// Generate proof obligations for every call to a spec-target function with .requires.
/// For each call site, we need to prove that the requires holds.
/// Only generates obligations for spec-target functions (those with original_body set).
fn render_requires_proof_obligations(
    program: &Program,
    impls_dir: &Path,
    prelude_imports: &[String],
    project_dir: &Path,
) -> anyhow::Result<()> {
    let specs_dir = impls_dir.parent().unwrap().join("Specs");
    let proofs_dir = project_dir.join("Proofs");
    fs::create_dir_all(&specs_dir)?;

    // Find spec-target functions that have .requires predicates
    // These are functions that had their body replaced and have .requires variants
    let mut spec_targets_with_requires: std::collections::HashMap<usize, (usize, &intermediate_theorem_format::Function)> = std::collections::HashMap::new();

    for (func_id, func) in program.functions.iter() {
        if func_id.variant == FunctionVariant::Requires && func_id.is_runtime() {
            // Check if the base function has original_body (meaning it's a spec-target)
            let base_func = program.functions.get(&FunctionID::new(func_id.base));
            if base_func.original_body.is_some() {
                spec_targets_with_requires.insert(func_id.base, (func.module_id, func));
            }
        }
    }

    // For each function in the program, check if it calls any spec-target function with requires
    for (caller_id, caller_func) in program.functions.iter() {
        // Only check base (Runtime) and Pure variants - skip other variants
        if !matches!(caller_id.variant, FunctionVariant::Runtime | FunctionVariant::Pure) {
            continue;
        }

        // Find all calls in this function
        let calls: Vec<_> = caller_func.body.calls().collect();

        for call_id in calls {
            // Check if this call is to a spec-target function with requires
            if let Some((callee_module_id, _requires_func)) = spec_targets_with_requires.get(&call_id.base) {
                let callee_func = program.functions.get(&FunctionID::new(call_id.base));
                let caller_module = program.modules.get(caller_func.module_id);
                let callee_module = program.modules.get(*callee_module_id);

                // Generate proof obligation
                let proof_name = format!(
                    "{}__calls__{}__requires",
                    caller_func.name,
                    callee_func.name
                );

                let mut proof_output = String::new();
                proof_output.push_str(&format!(
                    "-- Proof obligation: {} calls {} and must satisfy its requires\n\n",
                    caller_func.name, callee_func.name
                ));

                // Prelude imports
                for prelude_import in prelude_imports {
                    proof_output.push_str(&format!("import {}\n", prelude_import));
                }

                // Import modules
                let caller_namespace = escape::module_name_to_namespace(&caller_module.name);
                let callee_namespace = escape::module_name_to_namespace(&callee_module.name);

                proof_output.push_str(&format!(
                    "import Impls.{}.{}\n",
                    caller_module.package_name, caller_namespace
                ));
                if caller_module.package_name != callee_module.package_name || caller_module.name != callee_module.name {
                    proof_output.push_str(&format!(
                        "import Impls.{}.{}\n",
                        callee_module.package_name, callee_namespace
                    ));
                }

                proof_output.push('\n');
                proof_output.push_str(&format!("namespace {}\n\n", caller_namespace));

                // Generate theorem statement
                // TODO: Extract actual call arguments from the call site
                proof_output.push_str(&format!(
                    "-- TODO: Prove that when {} calls {}, the requires predicate holds\n",
                    caller_func.name, callee_func.name
                ));
                proof_output.push_str(&format!(
                    "-- axiom {}_obligation : True\n",
                    proof_name
                ));

                proof_output.push('\n');
                proof_output.push_str(&format!("end {}\n", caller_namespace));

                // Write to Specs/<caller_package>/<proof_name>.lean
                let spec_file = specs_dir
                    .join(&caller_module.package_name)
                    .join(format!("{}.lean", proof_name));

                if let Some(parent) = spec_file.parent() {
                    fs::create_dir_all(parent)?;
                }

                fs::write(spec_file, proof_output)?;
            }
        }
    }

    Ok(())
}
