// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders complete TheoremProgram to Lean files.

use intermediate_theorem_format::TheoremProgram;
use intermediate_theorem_format::analysis::analyze_purity;
use super::function_renderer::render_function;
use super::struct_renderer::render_struct;
use super::lean_writer::LeanWriter;
use crate::escape;
use std::collections::HashSet;
use std::fs;
use std::path::Path;

/// Render program to directory structure (organized by module hierarchy).
pub fn render_to_directory(program: &TheoremProgram, output_dir: &Path, prelude_imports: &[String]) -> anyhow::Result<()> {
    fs::create_dir_all(output_dir)?;

    println!("RENDERER: Copying native packages...");
    copy_native_packages(program, output_dir)?;
    println!("RENDERER: Native packages copied.");

    // Analyze purity for all functions
    let purity = analyze_purity(program);

    println!("RENDERER: Rendering {} modules...", program.modules.len());

    for (&module_id, module) in &program.modules {
        println!("RENDERER: Rendering module: {}", module.name);
        let mut module_output = String::new();

        module_output.push_str(&format!("-- Module: {}\n\n", module.name));

        // Prelude imports
        for prelude_import in prelude_imports {
            module_output.push_str(&format!("import {}\n", prelude_import));
        }

        // Module imports
        for &required_module_id in &module.required_imports {
            if let Some(required_module) = program.modules.get(&required_module_id) {
                let namespace = escape::module_name_to_namespace(&required_module.name);
                module_output.push_str(&format!("import Impls.{}.{}\n", required_module.package_name, namespace));
            }
        }

        // Native imports
        let has_native_functions = program.functions.values()
            .any(|f| f.module_id == module_id && f.is_native);
        if has_native_functions {
            let namespace_name = escape::module_name_to_namespace(&module.name);
            let natives_path = output_dir.join(&module.package_name).join(format!("{}Natives.lean", namespace_name));
            if natives_path.exists() {
                module_output.push_str(&format!("import Impls.{}.{}Natives\n", module.package_name, namespace_name));
            }
        }

        module_output.push('\n');

        let namespace_name = escape::module_name_to_namespace(&module.name);
        module_output.push_str(&format!("namespace {}\n\n", namespace_name));

        // Structs
        for (_, struct_def) in &program.structs {
            if struct_def.module_id == module_id {
                let mut writer = LeanWriter::new(String::new());
                render_struct(struct_def, &program.name_manager, &namespace_name, &mut writer);
                module_output.push_str(&writer.into_inner());
            }
        }

        // Functions
        let mut rendered_functions = HashSet::new();
        for (_, func) in &program.functions {
            if func.module_id != module_id {
                continue;
            }
            if rendered_functions.contains(&func.id) {
                continue;
            }
            if func.is_native {
                continue;
            }

            println!("RENDERER: Rendering function: {} in module {}", func.name, module.name);
            let mut writer = LeanWriter::new(String::new());
            render_function(func, program, &namespace_name, &purity, &mut writer);
            let rendered = writer.into_inner();
            println!("RENDERER: Function {} rendered ({} chars)", func.name, rendered.len());

            if !rendered.trim().is_empty() {
                module_output.push_str(&rendered);
                module_output.push('\n');
            }
            rendered_functions.insert(func.id);
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

    Ok(())
}

/// Copy native package implementations from lemmas directory.
fn copy_native_packages(program: &TheoremProgram, output_dir: &Path) -> anyhow::Result<()> {
    let lemmas_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
    let mut copied_modules = HashSet::new();

    for module in program.modules.values() {
        let has_native_functions = program.functions.values()
            .any(|f| f.module_id == module.id && f.is_native);

        if !has_native_functions {
            continue;
        }

        let module_key = format!("{}::{}", module.package_name, module.name);
        if copied_modules.contains(&module_key) {
            continue;
        }

        let lemma_file = format!("natives/{}/{}.lean", module.package_name, escape::capitalize_first(&module.name));
        let source_path = lemmas_dir.join(&lemma_file);

        if !source_path.exists() {
            continue;
        }

        let namespace = escape::module_name_to_namespace(&module.name);
        let dest_path = output_dir.join(&module.package_name).join(format!("{}Natives.lean", namespace));

        if let Some(parent) = dest_path.parent() {
            fs::create_dir_all(parent)?;
        }

        fs::copy(&source_path, &dest_path)?;
        copied_modules.insert(module_key);
    }

    Ok(())
}
