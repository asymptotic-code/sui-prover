// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Prelude File Management
//!
//! This module handles copying Prelude files (type definitions, helpers) to the output directory.

use anyhow::{Context, Result};
use log::{error, info};
use std::fs;
use std::path::{Path, PathBuf};

/// Prelude file manager
pub struct PreludeManager {
    /// Output directory (where Impls/ and Specs/ are)
    output_dir: PathBuf,

    /// Source directory for Prelude files (crates/move-prover-lean-backend/lemmas/)
    source_dir: PathBuf,
}

impl PreludeManager {
    /// Create a new prelude manager
    pub fn new(output_dir: PathBuf) -> Self {
        let source_dir = Self::find_prelude_source_dir(&output_dir);

        Self {
            output_dir,
            source_dir,
        }
    }

    /// Find the lemmas directory (contains Prelude and natives subdirs)
    fn find_prelude_source_dir(output_dir: &Path) -> PathBuf {
        let lemmas_subpath = "crates/move-prover-lean-backend/lemmas";

        // Try walking up from output_dir to find project root
        let mut current = output_dir.to_path_buf();
        while current.pop() {
            let candidate = current.join(lemmas_subpath);
            if candidate.join("Prelude").exists() {
                return candidate;
            }
        }

        // Try current working directory
        if let Ok(cwd) = std::env::current_dir() {
            let candidate = cwd.join(lemmas_subpath);
            if candidate.join("Prelude").exists() {
                return candidate;
            }

            // Try parent of current working directory
            if let Some(parent) = cwd.parent() {
                let candidate = parent.join(lemmas_subpath);
                if candidate.join("Prelude").exists() {
                    return candidate;
                }
            }
        }

        // Fallback to relative path from output_dir
        output_dir.join("../../").join(lemmas_subpath)
    }

    /// Initialize the Prelude directory structure and copy files
    pub fn initialize(&self) -> Result<()> {
        self.copy_prelude_files()
            .context("Failed to copy Prelude files")?;

        Ok(())
    }

    /// Get list of Prelude module names from source directory
    /// Returns module names like "Prelude.UInt128", "Prelude.Helpers", etc.
    pub fn get_prelude_imports(&self) -> Result<Vec<String>> {
        let prelude_source = self.source_dir.join("Prelude");

        if !prelude_source.exists() {
            return Ok(vec![]);
        }

        let entries = fs::read_dir(&prelude_source).context("Failed to read Prelude directory")?;

        let mut imports = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                if let Some(file_stem) = path.file_stem().and_then(|s| s.to_str()) {
                    imports.push(format!("Prelude.{}", file_stem));
                }
            }
        }

        // Sort for consistent ordering
        imports.sort();
        Ok(imports)
    }

    /// Copy Prelude files from lean backend to output directory
    fn copy_prelude_files(&self) -> Result<()> {
        let prelude_source = self.source_dir.join("Prelude");

        if !prelude_source.exists() {
            error!(
                "Prelude directory not found at: {}",
                prelude_source.display()
            );
            return Ok(());
        }

        info!("Copying Prelude files from: {}", prelude_source.display());

        let output_prelude = self.output_dir.join("Prelude");
        fs::create_dir_all(&output_prelude).context("Failed to create Prelude directory")?;

        let entries = fs::read_dir(&prelude_source).context("Failed to read Prelude directory")?;

        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("lean") {
                if let Some(file_name) = path.file_name() {
                    let dest = output_prelude.join(file_name);
                    fs::copy(&path, &dest).with_context(|| {
                        format!("Failed to copy {} to {}", path.display(), dest.display())
                    })?;
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_initialize() {
        let temp_dir = TempDir::new().unwrap();
        let manager = PreludeManager::new(temp_dir.path().to_path_buf());

        // This may or may not succeed depending on whether the source dir exists
        // In tests, we just verify it doesn't panic
        let _ = manager.initialize();
    }
}
