// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lean backend entry point
//!
//! Takes TheoremProgram and renders to Lean files.
//! ZERO logic, pure rendering.

use crate::renderer::render_to_directory;
use crate::runtime::run_lake_build;
use crate::lemma::LemmaFileGenerator;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use std::fs;
use std::path::Path;

/// Lean backend - translate IR to Lean
pub async fn run_backend(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
) -> anyhow::Result<()> {
    // Run translation pipeline
    let program = stackless_to_intermediate::translate_program(env, targets);

    // Clear output directory if it exists
    if output_dir.exists() {
        fs::remove_dir_all(output_dir)?;
    }

    // Create directory structure
    fs::create_dir_all(output_dir)?;
    fs::create_dir_all(output_dir.join("Impls"))?;
    fs::create_dir_all(output_dir.join("Aborts"))?;
    fs::create_dir_all(output_dir.join("Specs"))?;

    // Setup lemma system and copy Universal files
    let lemma_gen = LemmaFileGenerator::new(output_dir.to_path_buf());
    lemma_gen.initialize_directories()?;

    // Get Prelude imports from actual files being copied
    let prelude_imports = lemma_gen.get_prelude_imports()?;

    // Render to Lean in Impls/ directory with module organization
    println!("BACKEND: Starting render_to_directory...");
    let impls_dir = output_dir.join("Impls");
    render_to_directory(&program, &impls_dir, &prelude_imports)?;
    println!("BACKEND: render_to_directory completed.");

    // Generate lakefile and manifest
    println!("BACKEND: Writing lakefile...");
    crate::write_lakefile(output_dir, "sui_prover_output")?;
    println!("BACKEND: Lakefile written.");

    // Run lake build
    println!("BACKEND: Running lake build...");
    let output_str = output_dir.to_str()
        .ok_or_else(|| anyhow::anyhow!("Invalid output path"))?;

    match run_lake_build(output_str).await {
        Ok(output) => {
            println!("\n=== Lake Build Output ===");
            println!("{}", output);
            println!("=== Lake Build Succeeded ===\n");
            println!("Generated Lean files in: {}", output_dir.display());
            Ok(())
        }
        Err(e) => {
            Err(e)
        }
    }
}
