// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lake build execution for Lean projects

use anyhow::{anyhow, Result};
use log::debug;
use tokio::process::Command;

/// Runs `lake build` in the specified directory
///
/// Returns the combined stdout/stderr output on success, or an error if Lake fails.
pub async fn run_lake_build(project_dir: &str) -> Result<String> {
    debug!("running lake build in {}", project_dir);

    let output = tokio::time::timeout(
        std::time::Duration::from_secs(120),
        Command::new("lake")
            .arg("build")
            .current_dir(project_dir)
            .output()
    )
        .await
        .map_err(|_| anyhow!("lake build timed out after 120 seconds"))?
        .map_err(|e| anyhow!("failed to execute lake: {}", e))?;

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let combined_output = format!("{}\n{}", stdout, stderr);

    // Check for errors in stderr or non-zero exit code
    let has_error = !output.status.success()
        || stderr.contains(": error")
        || stderr.contains("error:");

    if has_error {
        Err(anyhow!(
            "lake build failed with exit code {}\n{}",
            output.status,
            combined_output
        ))
    } else {
        Ok(combined_output)
    }
}
