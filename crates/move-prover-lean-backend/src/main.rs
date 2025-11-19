// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lemma Manager CLI
//!
//! A command-line tool for managing lemmas in the Sui Prover lemma database.
//!
//! Usage:
//!   lemma-manager import <lean-file-or-dir>  # Import lemmas from Lean file(s)
//!   lemma-manager list                       # List all lemmas
//!   lemma-manager export <module>            # Export lemmas for a module
//!   lemma-manager status                     # Show cache statistics

use clap::{Parser, Subcommand};
use anyhow::{Context, Result, bail};
use std::path::PathBuf;
use std::process::Command;
use move_prover_lean_backend::lemma::cache::*;
use move_prover_lean_backend::lemma::generation::*;
use regex::Regex;

#[derive(Parser)]
#[command(name = "lemma-manager")]
#[command(about = "Manage lemmas in the Sui Prover lemma database", long_about = None)]
struct Cli {
    /// Path to the Move project directory
    #[arg(short, long, default_value = ".")]
    project: PathBuf,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Import lemmas from a Lean file or directory
    Import {
        /// Path to Lean file (.lean) or directory containing Lean files
        path: PathBuf,

        /// Module name (e.g., "Universal/UInt128")
        #[arg(short, long)]
        module: String,

        /// Category (e.g., "comparison", "arithmetic", "monotonicity")
        #[arg(short, long)]
        category: String,

        /// Skip lake build verification (not recommended)
        #[arg(long)]
        skip_verification: bool,
    },

    /// List all lemmas
    List {
        /// Filter by module
        #[arg(long)]
        module: Option<String>,

        /// Filter by status (proven, candidate, failed, invalidated)
        #[arg(long)]
        status: Option<String>,
    },

    /// Show lemma details
    Show {
        /// Lemma ID
        id: String,
    },

    /// Export lemmas for a module to Lean files
    Export {
        /// Module name (or 'all' for all modules)
        module: String,

        /// Output directory
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Show cache statistics
    Status,

    /// Remove a lemma from the cache
    Remove {
        /// Lemma ID
        id: String,
    },
}

/// Parse a Lean file and extract theorem/lemma declarations
fn parse_lean_file(path: &PathBuf) -> Result<Vec<(String, String, String)>> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read {}", path.display()))?;

    let mut lemmas = Vec::new();

    // Split by theorem/lemma keywords to find declarations
    let theorem_start_regex = Regex::new(
        r"(?m)^(?:theorem|lemma)\s+([a-zA-Z_][a-zA-Z0-9_]*)\s+"
    )?;

    let matches: Vec<_> = theorem_start_regex.find_iter(&content).collect();

    for i in 0..matches.len() {
        let start = matches[i].start();
        let end = if i + 1 < matches.len() {
            matches[i + 1].start()
        } else {
            content.len()
        };

        let decl_text = &content[start..end];

        // Extract name
        if let Some(cap) = theorem_start_regex.captures(decl_text) {
            let name = cap[1].trim().to_string();

            // Find := by to split statement and proof
            if let Some(by_pos) = decl_text.find(":= by") {
                let statement_part = &decl_text[..by_pos].trim();
                let proof_part = &decl_text[by_pos + 5..].trim();

                // Reconstruct full statement
                let statement = statement_part.to_string();

                // Clean up proof (remove trailing newlines and extra whitespace)
                let proof_clean = proof_part.lines()
                    .map(|l| l.trim())
                    .filter(|l| !l.is_empty())
                    .collect::<Vec<_>>()
                    .join("\n  ");

                lemmas.push((name, statement, proof_clean));
            }
        }
    }

    Ok(lemmas)
}

/// Verify that Lean file builds successfully
fn verify_lean_file(path: &PathBuf) -> Result<()> {
    println!("Verifying {} with lake...", path.display());

    // Create a temporary test directory
    let temp_dir = std::env::temp_dir().join("sui-prover-lemma-test");
    std::fs::create_dir_all(&temp_dir)?;

    // Copy the file to temp directory
    let file_name = path.file_name()
        .context("Invalid file path")?;
    let temp_file = temp_dir.join(file_name);
    std::fs::copy(path, &temp_file)?;

    // Run lake env lean on the file
    let output = Command::new("lake")
        .args(&["env", "lean", temp_file.to_str().unwrap()])
        .current_dir(&temp_dir)
        .output()
        .context("Failed to execute lake. Is Lean 4 installed?")?;

    // Clean up
    let _ = std::fs::remove_dir_all(&temp_dir);

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        bail!("Lake build failed:\n{}", stderr);
    }

    // Check for errors in output
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if stderr.contains("error:") || stderr.contains("Error:") {
        bail!("Lean compilation errors found:\n{}", stderr);
    }

    if stdout.contains("error:") || stdout.contains("Error:") {
        bail!("Lean compilation errors found:\n{}", stdout);
    }

    println!("✓ Verification successful");
    Ok(())
}

/// Validate that proof doesn't contain sorry or axiom
fn validate_proof(proof: &str, name: &str) -> Result<()> {
    if proof.contains("sorry") {
        bail!("Lemma '{}' contains 'sorry'. All lemmas must be fully proven.", name);
    }
    if proof.contains("axiom") {
        bail!("Lemma '{}' contains 'axiom'. Lemmas must be proven, not assumed.", name);
    }
    Ok(())
}

/// Validate that statement uses theorem/lemma, not axiom
fn validate_statement(statement: &str, name: &str) -> Result<()> {
    if statement.trim().starts_with("axiom") {
        bail!("Lemma '{}' must use 'theorem' or 'lemma', not 'axiom'.", name);
    }
    Ok(())
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Initialize cache manager
    let mut manager = LemmaCacheManager::new()?;
    manager.load_project_cache(&cli.project)?;

    match cli.command {
        Commands::Import { path, module, category, skip_verification } => {
            // Collect all .lean files
            let mut lean_files = Vec::new();

            if path.is_file() {
                if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                    lean_files.push(path.clone());
                } else {
                    bail!("File must have .lean extension: {}", path.display());
                }
            } else if path.is_dir() {
                // Recursively find all .lean files
                for entry in walkdir::WalkDir::new(&path) {
                    let entry = entry?;
                    if entry.path().extension().and_then(|s| s.to_str()) == Some("lean") {
                        lean_files.push(entry.path().to_path_buf());
                    }
                }
            } else {
                bail!("Path does not exist: {}", path.display());
            }

            if lean_files.is_empty() {
                bail!("No .lean files found in: {}", path.display());
            }

            println!("Found {} Lean file(s) to import", lean_files.len());

            let mut total_imported = 0;
            let mut total_updated = 0;

            for lean_file in &lean_files {
                println!("\nProcessing: {}", lean_file.display());

                // Verify the file builds (unless skip flag is set)
                if !skip_verification {
                    verify_lean_file(lean_file)?;
                }

                // Parse lemmas from the file
                let parsed_lemmas = parse_lean_file(lean_file)?;
                println!("  Found {} lemma(s)", parsed_lemmas.len());

                // Add each lemma to the cache
                for (name, statement, proof) in parsed_lemmas {
                    // Validate
                    validate_statement(&statement, &name)?;
                    validate_proof(&proof, &name)?;

                    // Check if lemma already exists
                    let exists = if let Some(cache) = manager.current_cache() {
                        cache.lemmas.contains_key(&name)
                    } else {
                        false
                    };

                    let lemma = CachedLemma {
                        lemma_id: name.clone(),
                        module: module.clone(),
                        function: None,
                        category: category.clone(),
                        statement: statement.clone(),
                        proof: Some(proof.clone()),
                        dependencies: vec![],
                        status: LemmaStatus::Proven,
                        generation_method: GenerationMethod::Manual,
                        confidence: 1.0,
                        difficulty: Difficulty::Unknown,
                        used_by: vec![],
                        created_at: chrono::Utc::now(),
                        proven_at: Some(chrono::Utc::now()),
                        proof_time_ms: None,
                        version: 1,
                    };

                    if let Some(cache) = manager.current_cache_mut() {
                        cache.add_lemma(lemma);
                    }

                    if exists {
                        println!("  ✓ Updated: {}", name);
                        total_updated += 1;
                    } else {
                        println!("  ✓ Imported: {}", name);
                        total_imported += 1;
                    }
                }
            }

            // Save the cache
            manager.save_project_cache(&cli.project)?;

            println!("\n✅ Import complete!");
            println!("   {} new lemma(s)", total_imported);
            println!("   {} updated lemma(s)", total_updated);
        }

        Commands::List { module, status } => {
            if let Some(cache) = manager.current_cache() {
                let mut lemmas: Vec<_> = cache.lemmas.values().collect();

                // Filter by module
                if let Some(ref m) = module {
                    lemmas.retain(|l| &l.module == m);
                }

                // Filter by status
                if let Some(ref s) = status {
                    let filter_status = match s.to_lowercase().as_str() {
                        "proven" => LemmaStatus::Proven,
                        "candidate" => LemmaStatus::Candidate,
                        "failed" => LemmaStatus::Failed,
                        "invalidated" => LemmaStatus::Invalidated,
                        _ => {
                            panic!("BUG: Unknown lemma status: {}", s);
                        }
                    };
                    lemmas.retain(|l| l.status == filter_status);
                }

                println!("Found {} lemma(s):\n", lemmas.len());
                for lemma in lemmas {
                    println!("  {} ({:?})", lemma.lemma_id, lemma.status);
                    println!("    Module: {}", lemma.module);
                    if let Some(ref f) = lemma.function {
                        println!("    Function: {}", f);
                    }
                    println!("    Category: {}", lemma.category);
                    if !lemma.dependencies.is_empty() {
                        println!("    Dependencies: {:?}", lemma.dependencies);
                    }
                    println!();
                }
            } else {
                println!("No cache loaded");
            }
        }

        Commands::Show { id } => {
            if let Some(lemma) = manager.find_lemma(&id) {
                println!("Lemma: {}\n", lemma.lemma_id);
                println!("Module: {}", lemma.module);
                if let Some(ref f) = lemma.function {
                    println!("Function: {}", f);
                }
                println!("Category: {}", lemma.category);
                println!("Status: {:?}", lemma.status);
                println!("Generation: {:?}", lemma.generation_method);
                println!("Confidence: {:.2}", lemma.confidence);
                println!("Difficulty: {:?}", lemma.difficulty);
                println!("\nStatement:");
                println!("{}\n", lemma.statement);

                if let Some(ref proof) = lemma.proof {
                    println!("Proof:");
                    println!("{}\n", proof);
                } else {
                    println!("Proof: (not yet proven)\n");
                }

                if !lemma.dependencies.is_empty() {
                    println!("Dependencies: {:?}", lemma.dependencies);
                }

                if !lemma.used_by.is_empty() {
                    println!("Used by: {:?}", lemma.used_by);
                }

                println!("\nCreated: {}", lemma.created_at);
                if let Some(proven_at) = lemma.proven_at {
                    println!("Proven: {}", proven_at);
                    if let Some(time) = lemma.proof_time_ms {
                        println!("Proof time: {}ms", time);
                    }
                }
            } else {
                println!("Lemma not found: {}", id);
            }
        }

        Commands::Export { module, output } => {
            let output_dir = output.unwrap_or_else(|| cli.project.join("output"));

            if let Some(cache) = manager.current_cache() {
                let generator = LemmaFileGenerator::new(output_dir.clone());
                generator.initialize_directories()?;

                if module == "all" {
                    // Export all modules
                    let mut modules: std::collections::HashSet<&str> =
                        std::collections::HashSet::new();

                    for lemma in cache.lemmas.values() {
                        modules.insert(&lemma.module);
                    }

                    for mod_name in modules {
                        let lemmas: Vec<_> = cache.lemmas_for_module(mod_name).collect();
                        if !lemmas.is_empty() {
                            let path = generator.generate_dependency_lemma_file(
                                mod_name,
                                &lemmas,
                            )?;
                            println!("Exported {} lemmas to: {}", lemmas.len(), path.display());
                        }
                    }

                    // Generate registry
                    generator.create_lemma_registry(cache)?;
                    println!("\nGenerated lemma registry");
                } else {
                    // Export specific module
                    let lemmas: Vec<_> = cache.lemmas_for_module(&module).collect();

                    if lemmas.is_empty() {
                        println!("No lemmas found for module: {}", module);
                    } else {
                        let path = generator.generate_dependency_lemma_file(
                            &module,
                            &lemmas,
                        )?;
                        println!("Exported {} lemmas to: {}", lemmas.len(), path.display());
                    }
                }
            } else {
                println!("No cache loaded");
            }
        }

        Commands::Status => {
            if let Some(cache) = manager.current_cache() {
                println!("=== Lemma Cache Status ===\n");
                println!("Project hash: {}", cache.project_hash);
                println!("Last updated: {}\n", cache.last_updated);

                println!("Lemmas:");
                println!("  Total: {}", cache.lemmas.len());
                println!("  Proven: {}", cache.proven_lemmas().count());
                println!("  Candidates: {}",
                    cache.lemmas.values()
                        .filter(|l| l.status == LemmaStatus::Candidate)
                        .count());
                println!("  Failed: {}",
                    cache.lemmas.values()
                        .filter(|l| l.status == LemmaStatus::Failed)
                        .count());

                println!("\nProof strategies: {}", cache.strategies.len());

                // Group by module
                let mut modules: std::collections::HashMap<&str, usize> =
                    std::collections::HashMap::new();
                for lemma in cache.lemmas.values() {
                    *modules.entry(&lemma.module).or_insert(0) += 1;
                }

                println!("\nLemmas by module:");
                let mut sorted: Vec<_> = modules.iter().collect();
                sorted.sort_by_key(|(_, count)| std::cmp::Reverse(*count));
                for (module, count) in sorted {
                    println!("  {}: {}", module, count);
                }
            } else {
                println!("No cache loaded");
            }
        }

        Commands::Remove { id } => {
            if let Some(cache) = manager.current_cache_mut() {
                if cache.lemmas.remove(&id).is_some() {
                    manager.save_project_cache(&cli.project)?;
                    println!("Removed lemma: {}", id);
                } else {
                    println!("Lemma not found: {}", id);
                }
            }
        }
    }

    Ok(())
}
