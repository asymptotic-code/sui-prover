// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lean backend entry point
//!
//! Takes TheoremProgram and renders to Lean files.
//! ZERO logic, pure rendering.

use crate::prelude::PreludeManager;
use crate::renderer::render_to_directory;
use crate::runtime::run_lake_build;
use intermediate_theorem_format::insert_bool_coercions;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use stackless_to_intermediate::ProgramBuilder;
use std::fs;
use std::path::Path;

/// Recursively copy a directory tree
fn copy_dir_recursive(src: &Path, dst: &Path) -> anyhow::Result<()> {
    if !src.is_dir() {
        return Ok(());
    }

    fs::create_dir_all(dst)?;

    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());

        if src_path.is_dir() {
            copy_dir_recursive(&src_path, &dst_path)?;
        } else {
            fs::copy(&src_path, &dst_path)?;
        }
    }

    Ok(())
}

/// Lean backend - translate IR to Lean
///
/// - `env`: The Move global environment
/// - `targets`: The function targets holder
/// - `output_dir`: Where to write generated Lean files (e.g., `<package>/output`)
/// - `package_dir`: The Move package root (e.g., `<package>/`), used to find user proofs in `sources/lean/`
pub async fn run_backend(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    package_dir: &Path,
) -> anyhow::Result<()> {
    // Run translation pipeline
    let mut program = ProgramBuilder::new(env).build(targets);

    // Insert ToBool coercions for If/While conditions in runtime functions
    // This is needed because comparisons return Prop in Lean, but `if` requires Bool
    insert_bool_coercions(&mut program);

    // Clear output directory if it exists
    if output_dir.exists() {
        fs::remove_dir_all(output_dir)?;
    }

    // Create directory structure
    fs::create_dir_all(output_dir)?;
    fs::create_dir_all(output_dir.join("Impls"))?;
    fs::create_dir_all(output_dir.join("Aborts"))?;
    fs::create_dir_all(output_dir.join("Specs"))?;
    fs::create_dir_all(output_dir.join("Proofs"))?;

    // Copy user proofs from sources/lean/ to output/Proofs/
    let user_proofs_src = package_dir.join("sources").join("lean");
    let proofs_dest = output_dir.join("Proofs");
    if user_proofs_src.exists() {
        copy_dir_recursive(&user_proofs_src, &proofs_dest)?;
    }

    // Copy Prelude files
    let prelude_manager = PreludeManager::new(output_dir.to_path_buf());
    prelude_manager.initialize()?;

    // Get Prelude imports from actual files being copied
    let prelude_imports = prelude_manager.get_prelude_imports()?;

    // Render to Lean in Impls/ directory with module organization
    // User proofs are in output/Proofs/ (copied from sources/lean/)
    let impls_dir = output_dir.join("Impls");
    render_to_directory(
        &program,
        &impls_dir,
        &prelude_imports,
        output_dir,
        &proofs_dest,
    )?;

    // Generate lakefile and manifest
    crate::write_lakefile(output_dir, "sui_prover_output")?;

    // Run lake build
    let output_str = output_dir
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("Invalid output path"))?;

    match run_lake_build(output_str).await {
        Ok(output) => {
            println!("\n=== Lake Build Output ===");
            println!("{}", output);
            println!("=== Lake Build Succeeded ===\n");
            println!("Generated Lean files in: {}", output_dir.display());
            Ok(())
        }
        Err(e) => Err(e),
    }
}
