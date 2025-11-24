// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Utilities for extracting Move package information

use std::fs::read_to_string;
use move_model::model::{GlobalEnv, ModuleEnv};
use std::path::{Path, PathBuf};
use toml::{from_str, Value};

/// Extract package name from module by parsing its source location and finding Move.toml
/// For native/framework modules without a Move.toml, returns the module's address as package name
pub fn extract_package_name(env: &GlobalEnv, module_env: &ModuleEnv) -> String {
    let file_path = env.get_file(module_env.get_loc().file_id());
    find_package_name_from_path(Path::new(file_path))
        .unwrap_or_else(|| format!("{}", module_env.get_name().addr()))
}

/// Find the Move.toml file by walking up from the given path and extract the package name
fn find_package_name_from_path(start_path: &Path) -> Option<String> {
    let current_dir = start_path.parent()?;
    parse_package_name_from_toml(current_dir.join("Move.toml"))
        .or_else(|| find_package_name_from_path(current_dir))
}

/// Parse the package name from a Move.toml file using proper TOML parsing
fn parse_package_name_from_toml(toml_path: PathBuf) -> Option<String> {
    Some(from_str::<Value>(&read_to_string(toml_path).ok()?).ok()?
        .get("package")?
        .get("name")?
        .as_str()?
        .to_string())
}
