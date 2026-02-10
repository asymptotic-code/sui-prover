//! Specification hierarchy visualization and tree generation.
//!
//! This module provides functionality to generate and display specification call hierarchies,
//! showing how specs call other specs and functions. It supports two output modes:
//! - File output: Writes detailed call trees to .log.txt files showing all functions and their specs
//! - Terminal output: Displays only opaque specs (excludes no_opaque specs) during verification (verbose mode)
//!
//! The hierarchies respect opaque boundaries (specs without `no_opaque`) and filter out
//! system functions from standard libraries.

use crate::function_target_pipeline::FunctionTargetsHolder;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, QualifiedId};
use num::BigUint;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

/// File extension for spec hierarchy log files.
const LOG_FILE_EXTENSION: &str = ".log.txt";

/// Label appended to scenario spec names in the tree.
const SCENARIO_LABEL: &str = "[scenario]";

/// Information about a function call, including its display name and associated spec (if any).
#[derive(Debug)]
struct CallInfo {
    /// The display name to show in the tree (either function name or spec name)
    display_name: String,
    /// The spec ID if this function has an associated spec in the current targets
    spec_id: Option<QualifiedId<FunId>>,
}

/// Generates and writes specification hierarchy trees to log files.
///
/// For each spec in the targets, creates a `.log.txt` file in the output directory
/// showing the complete call hierarchy including:
/// - All functions called by the spec's underlying implementation
/// - Spec properties (prove, no_opaque) for functions that have specs
/// - System functions are excluded (stdlib, Sui framework, etc.)
/// - Tree structure with proper indentation using box-drawing characters
///
/// # Tree Traversal
/// - Recurses into functions without specs to find nested specs
/// - Stops recursing at opaque specs (specs without `no_opaque`)
/// - Recurses into `no_opaque` specs since the prover uses their implementation
/// - Prevents infinite recursion by tracking displayed functions
///
/// # Arguments
/// * `env` - Global environment containing all function and module information
/// * `targets` - Holder containing all specs and their relationships
/// * `output_dir` - Directory where .log.txt files will be written
pub fn display_spec_hierarchy(env: &GlobalEnv, targets: &FunctionTargetsHolder, output_dir: &Path) {
    let excluded_addresses = get_excluded_addresses();

    for spec_id in targets.specs() {
        let spec_env = env.get_function(*spec_id);
        let spec_name = spec_env.get_full_name_str();

        if let Some(fun_id) = targets.get_fun_by_spec(spec_id) {
            let func_env = env.get_function(*fun_id);
            let header = func_env.get_full_name_str();
            write_spec_log_file(
                env,
                targets,
                &func_env,
                spec_name,
                &header,
                output_dir,
                &excluded_addresses,
            );
        } else if targets.is_scenario_spec(spec_id) {
            let header = format!("{} {}", spec_env.get_full_name_str(), SCENARIO_LABEL);
            write_spec_log_file(
                env,
                targets,
                &spec_env,
                spec_name,
                &header,
                output_dir,
                &excluded_addresses,
            );
        }
    }
}

fn get_excluded_addresses() -> [BigUint; 4] {
    [
        1u16.into(),      // MoveStdlib
        2u16.into(),      // Sui
        3u16.into(),      // SuiSystem
        0xdee9u16.into(), // DeepBook address
    ]
}

/// Writes a single spec's hierarchy tree to a log file.
///
/// Creates a file named `{spec_name}.log.txt` containing:
/// - Header line (function name or scenario name)
/// - Complete call tree using `build_implementation_tree`
///
/// Errors during file writing are logged to stderr but don't fail the verification.
fn write_spec_log_file(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    func_env: &FunctionEnv,
    spec_name: String,
    header: &str,
    output_dir: &Path,
    excluded_addresses: &[BigUint],
) {
    let log_file_path = output_dir.join(format!("{}{}", spec_name, LOG_FILE_EXTENSION));

    let mut content = String::new();
    let mut displayed = BTreeSet::new();

    content.push_str(&format!("{}\n", header));

    build_implementation_tree(
        env,
        targets,
        func_env,
        "",
        excluded_addresses,
        &mut displayed,
        &mut content,
    );

    if let Err(e) = fs::write(&log_file_path, content) {
        eprintln!("Failed to write log file {:?}: {}", log_file_path, e);
    }
}

fn is_system_function(func_env: &FunctionEnv, excluded_addresses: &[BigUint]) -> bool {
    let module_addr = func_env.module_env.get_name().addr();
    let module_name = func_env
        .module_env
        .get_name()
        .name()
        .display(func_env.module_env.env.symbol_pool())
        .to_string();

    excluded_addresses.contains(module_addr)
        || GlobalEnv::SPECS_MODULES_NAMES.contains(&module_name.as_str())
}

/// Gets display information for a function call, including its name and associated spec.
///
/// If the function has a spec in the current targets, returns the spec's name.
/// Otherwise, returns the function's own name.
fn get_call_display_info(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    called_id: &QualifiedId<FunId>,
) -> CallInfo {
    if let Some(spec_id) = targets.get_spec_by_fun(called_id) {
        let spec_env = env.get_function(*spec_id);
        CallInfo {
            display_name: spec_env.get_full_name_str(),
            spec_id: Some(*spec_id),
        }
    } else {
        let called_env = env.get_function(*called_id);
        CallInfo {
            display_name: called_env.get_full_name_str(),
            spec_id: None,
        }
    }
}

/// Formats spec properties as a string for display in the tree.
///
/// Returns a string like " (prove, no_opaque)" or empty string if no properties.
fn format_spec_properties(targets: &FunctionTargetsHolder, spec_id: &QualifiedId<FunId>) -> String {
    let mut properties = Vec::new();

    if targets.is_verified_spec(spec_id) {
        properties.push("prove");
    }
    if targets.omits_opaque(spec_id) {
        properties.push("no_opaque");
    }

    if properties.is_empty() {
        String::new()
    } else {
        format!(" ({})", properties.join(", "))
    }
}

/// Generates tree branch characters and the prefix for child nodes.
///
/// Returns (branch_str, next_prefix) where:
/// - branch_str: "├──" or "└──" depending on if this is the last child
/// - next_prefix: "│  " or "   " for the next level of recursion
fn get_tree_branch(is_last: bool, prefix: &str) -> (String, String) {
    if is_last {
        (format!("{}└──", prefix), format!("{}   ", prefix))
    } else {
        (format!("{}├──", prefix), format!("{}│  ", prefix))
    }
}

/// Recursively builds the implementation tree for log files.
///
/// Shows ALL functions in the call graph with their associated specs (if any).
/// Stops recursing at opaque specs (without `no_opaque`), but recurses into
/// `no_opaque` specs since the prover uses their implementation.
///
/// # Arguments
/// * `displayed` - Set tracking already displayed functions to prevent cycles
/// * `content` - String buffer where the tree is written
fn build_implementation_tree(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    func_env: &FunctionEnv,
    prefix: &str,
    excluded_addresses: &[BigUint],
    displayed: &mut BTreeSet<QualifiedId<FunId>>,
    content: &mut String,
) {
    let filtered_calls: Vec<_> = func_env
        .get_called_functions()
        .into_iter()
        .filter(|called_id| {
            let called_env = env.get_function(*called_id);
            !is_system_function(&called_env, excluded_addresses)
        })
        .collect();

    for (i, called_id) in filtered_calls.iter().enumerate() {
        let is_last = i == filtered_calls.len() - 1;
        let (branch, next_prefix) = get_tree_branch(is_last, prefix);

        let call_info = get_call_display_info(env, targets, called_id);

        let props_str = call_info
            .spec_id
            .map(|spec_id| format_spec_properties(targets, &spec_id))
            .unwrap_or_default();

        content.push_str(&format!(
            "{} {}{}\n",
            branch, call_info.display_name, props_str
        ));

        let should_recurse = if let Some(spec_id) = call_info.spec_id {
            targets.omits_opaque(&spec_id)
        } else {
            true
        };

        if should_recurse && !displayed.contains(called_id) {
            displayed.insert(*called_id);
            let called_env = env.get_function(*called_id);
            build_implementation_tree(
                env,
                targets,
                &called_env,
                &next_prefix,
                excluded_addresses,
                displayed,
                content,
            );
        }
    }
}

/// Displays a spec-only call tree to the terminal during verification.
///
/// Shows the specification hierarchy for a single spec, displaying:
/// - First: specs called directly from the spec function itself
/// - Then: the target function marked with 🎯
/// - Under the target function: its dependencies
///
/// # Limitations
/// Unlike `display_spec_hierarchy`, this function only sees specs in the current
/// verification context (`targets`). Specs from other modules will not be shown
/// even if they exist in the package.
///
/// # Behavior
/// - Traverses the underlying function's call graph
/// - Only displays opaque specs (specs without `no_opaque`)
/// - Does NOT display `no_opaque` specs, but recurses through them to find nested opaque specs
/// - Recursively explores functions without specs to find nested specs
/// - Stops recursing at opaque specs (prover uses the spec itself)
/// - Excludes the root spec from its own tree
/// - Returns early for scenario specs (no underlying implementation)
///
/// # Arguments
/// * `env` - Global environment containing all function information
/// * `targets` - Holder containing specs in the current verification context
/// * `spec_id` - The spec ID to display the tree for
pub fn display_spec_tree_terminal(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    spec_id: &QualifiedId<FunId>,
) {
    let excluded_addresses = get_excluded_addresses();

    // Get the underlying function being verified
    let fun_id = if let Some(fun_id) = targets.get_fun_by_spec(spec_id) {
        *fun_id
    } else {
        return;
    };
    let func_env = env.get_function(fun_id);
    let spec_env = env.get_function(*spec_id);

    // Display spec function's dependencies (skipping the target function itself)
    let mut displayed = BTreeSet::new();
    build_spec_only_tree(
        env,
        targets,
        &spec_env,
        "",
        &excluded_addresses,
        &mut displayed,
        spec_id,
        Some(&fun_id),
    );

    // Display the target function with 🎯
    let (branch, next_prefix) = get_tree_branch(true, "");
    println!("{} 🎯{}", branch, func_env.get_full_name_str());

    // Display the target function's dependencies
    displayed.clear();
    build_spec_only_tree(
        env,
        targets,
        &func_env,
        &next_prefix,
        &excluded_addresses,
        &mut displayed,
        spec_id,
        None,
    );
}

/// Counts specs that will be displayed at the current tree level.
/// This includes both direct specs and specs found by recursing through
/// transparent (no-spec) functions, since those render at the same indentation.
fn count_displayable_specs(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    filtered_calls: &[QualifiedId<FunId>],
    excluded_addresses: &[BigUint],
    visited: &mut BTreeSet<QualifiedId<FunId>>,
    root_spec_id: &QualifiedId<FunId>,
    spec_target_fun_id: Option<&QualifiedId<FunId>>,
) -> usize {
    let mut count = 0;
    for called_id in filtered_calls {
        let spec_id = targets.get_spec_by_fun(called_id);
        let will_display = if let Some(sid) = spec_id {
            *sid != *root_spec_id && !targets.omits_opaque(sid)
        } else {
            false
        };
        if will_display {
            count += 1;
        } else {
            let should_recurse = spec_id.map_or(true, |sid| *sid != *root_spec_id);
            if should_recurse && !visited.contains(called_id) {
                visited.insert(*called_id);
                let called_env = env.get_function(*called_id);
                let child_calls: Vec<_> = called_env
                    .get_called_functions()
                    .into_iter()
                    .filter(|cid| {
                        if spec_target_fun_id == Some(cid) {
                            return false;
                        }
                        let ce = env.get_function(*cid);
                        !is_system_function(&ce, excluded_addresses)
                            || targets.get_spec_by_fun(cid).is_some()
                    })
                    .collect();
                count += count_displayable_specs(
                    env,
                    targets,
                    &child_calls,
                    excluded_addresses,
                    visited,
                    root_spec_id,
                    spec_target_fun_id,
                );
            }
        }
    }
    count
}

/// Recursively builds a spec-only tree for terminal output.
///
/// Similar to `build_implementation_tree` but:
/// - Only DISPLAYS opaque specs (specs without `no_opaque`) in the current targets
/// - Does NOT display `no_opaque` specs, but RECURSES through them to find nested opaque specs
/// - Still RECURSES through functions without specs to find nested specs
/// - Excludes the root spec from appearing in its own tree
///
/// # Arguments
/// * `root_spec_id` - The spec being displayed; excluded from the tree
/// * `displayed` - Set tracking already displayed functions to prevent cycles
/// * `spec_target_fun_id` - Optional function to skip (used to exclude target function when traversing spec)
fn build_spec_only_tree(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    func_env: &FunctionEnv,
    prefix: &str,
    excluded_addresses: &[BigUint],
    displayed: &mut BTreeSet<QualifiedId<FunId>>,
    root_spec_id: &QualifiedId<FunId>,
    spec_target_fun_id: Option<&QualifiedId<FunId>>,
) {
    let filtered_calls: Vec<_> = func_env
        .get_called_functions()
        .into_iter()
        .filter(|called_id| {
            if spec_target_fun_id == Some(called_id) {
                return false;
            }
            let called_env = env.get_function(*called_id);
            // keep system functions that have a spec registered in the current targets
            !is_system_function(&called_env, excluded_addresses)
                || targets.get_spec_by_fun(called_id).is_some()
        })
        .collect();

    let total_displayable = {
        let mut visited = displayed.clone();
        count_displayable_specs(
            env,
            targets,
            &filtered_calls,
            excluded_addresses,
            &mut visited,
            root_spec_id,
            spec_target_fun_id,
        )
    };

    let mut spec_index = 0;
    build_spec_only_tree_inner(
        env,
        targets,
        &filtered_calls,
        prefix,
        excluded_addresses,
        displayed,
        root_spec_id,
        spec_target_fun_id,
        &mut spec_index,
        total_displayable,
    );
}

fn build_spec_only_tree_inner(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    filtered_calls: &[QualifiedId<FunId>],
    prefix: &str,
    excluded_addresses: &[BigUint],
    displayed: &mut BTreeSet<QualifiedId<FunId>>,
    root_spec_id: &QualifiedId<FunId>,
    spec_target_fun_id: Option<&QualifiedId<FunId>>,
    spec_index: &mut usize,
    total_displayable: usize,
) {
    for called_id in filtered_calls.iter() {
        let call_info = get_call_display_info(env, targets, called_id);
        let spec_id = targets.get_spec_by_fun(called_id);

        let will_display = if let Some(sid) = spec_id {
            *sid != *root_spec_id && !targets.omits_opaque(sid)
        } else {
            false
        };

        if will_display {
            let is_last = *spec_index == total_displayable - 1;
            let (branch, next_prefix) = get_tree_branch(is_last, prefix);

            let props_str = format_spec_properties(targets, spec_id.unwrap());
            println!("{} {}{}", branch, call_info.display_name, props_str);

            *spec_index += 1;

            let should_recurse = targets.omits_opaque(spec_id.unwrap());
            if should_recurse && !displayed.contains(called_id) {
                displayed.insert(*called_id);
                let called_env = env.get_function(*called_id);
                build_spec_only_tree(
                    env,
                    targets,
                    &called_env,
                    &next_prefix,
                    excluded_addresses,
                    displayed,
                    root_spec_id,
                    spec_target_fun_id,
                );
            }
        } else {
            let should_recurse = spec_id.map_or(true, |sid| *sid != *root_spec_id);
            if should_recurse && !displayed.contains(called_id) {
                displayed.insert(*called_id);
                let called_env = env.get_function(*called_id);
                let child_calls: Vec<_> = called_env
                    .get_called_functions()
                    .into_iter()
                    .filter(|cid| {
                        if spec_target_fun_id == Some(cid) {
                            return false;
                        }
                        let ce = env.get_function(*cid);
                        !is_system_function(&ce, excluded_addresses)
                            || targets.get_spec_by_fun(cid).is_some()
                    })
                    .collect();
                build_spec_only_tree_inner(
                    env,
                    targets,
                    &child_calls,
                    prefix,
                    excluded_addresses,
                    displayed,
                    root_spec_id,
                    spec_target_fun_id,
                    spec_index,
                    total_displayable,
                );
            }
        }
    }
}
