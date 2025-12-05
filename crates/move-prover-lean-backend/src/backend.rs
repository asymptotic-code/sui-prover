// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lean backend entry point
//!
//! Takes TheoremProgram and renders to Lean files.
//! ZERO logic, pure rendering.

use crate::prelude::PreludeManager;
use crate::renderer::render_to_directory;
use crate::runtime::run_lake_build;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use stackless_to_intermediate::ProgramBuilder;
use std::fs;
use std::path::Path;

/// Lean backend - translate IR to Lean
pub async fn run_backend(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    output_dir: &Path,
    generate_only: bool,
) -> anyhow::Result<()> {
    // Run translation pipeline
    let program = ProgramBuilder::new(env).build(targets);

    // Clear output directory if it exists
    if output_dir.exists() {
        fs::remove_dir_all(output_dir)?;
    }

    // Create directory structure
    fs::create_dir_all(output_dir)?;
    fs::create_dir_all(output_dir.join("Impls"))?;
    fs::create_dir_all(output_dir.join("Aborts"))?;
    fs::create_dir_all(output_dir.join("Specs"))?;

    // Copy Prelude files
    let prelude_manager = PreludeManager::new(output_dir.to_path_buf());
    prelude_manager.initialize()?;

    // Get Prelude imports from actual files being copied
    let prelude_imports = prelude_manager.get_prelude_imports()?;

    // Render to Lean in Impls/ directory with module organization
    let impls_dir = output_dir.join("Impls");
    render_to_directory(&program, &impls_dir, &prelude_imports)?;

    // Generate lakefile and manifest
    crate::write_lakefile(output_dir, "sui_prover_output")?;

    // Skip lake build if generate_only is true
    if generate_only {
        println!("✓ Lean code generated (skipping lake build)");
        return Ok(());
    }

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
