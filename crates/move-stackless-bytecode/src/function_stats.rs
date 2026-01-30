use move_binary_format::file_format::Visibility;
use move_compiler::shared::known_attributes::AttributeKind_;
use move_model::{
    ast::Attribute,
    model::{FunId, FunctionEnv, GlobalEnv, QualifiedId},
};
use std::collections::BTreeMap;

use crate::package_targets::PackageTargets;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStatus {
    Skipped,
    NoSpec,
    NoProve,
    SuccessfulProof,
    IgnoreAborts,
}

impl std::fmt::Display for ProofStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofStatus::SuccessfulProof => write!(f, "✅ has spec"),
            ProofStatus::IgnoreAborts => write!(f, "⚠️  spec but with ignore_abort"),
            ProofStatus::Skipped => write!(f, "⏭️  skipped spec"),
            ProofStatus::NoProve => write!(f, "✖️ no prove"),
            ProofStatus::NoSpec => write!(f, "❌ no spec"),
        }
    }
}

/// Checks if a function has a specific attribute (e.g., "spec_only", "test_only").
fn has_attribute(func_env: &FunctionEnv, attr_name: &str) -> bool {
    func_env.get_attributes().iter().any(|attr| {
        matches!(
            attr,
            Attribute::Apply(_, name, _) | Attribute::Assign(_, name, _)
            if name.display(func_env.symbol_pool()).to_string() == attr_name
        )
    })
}

/// Determines if a function should be included in statistics.
///
/// Filters out:
/// - Non-public and non-entry functions
/// - Functions with `spec_only` attribute
/// - Functions with `test_only` attribute
/// - Spec functions themselves
fn should_include_function(func_env: &FunctionEnv, targets: &PackageTargets) -> bool {
    if func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::Mode)
        .is_some()
    {
        return false;
    }
    // Include public functions and entry functions (entry functions can have any visibility)
    if func_env.visibility() != Visibility::Public && !func_env.is_entry() {
        return false;
    }
    if func_env
        .get_toplevel_attributes()
        .get_(&AttributeKind_::SpecOnly)
        .is_some()
    {
        return false;
    }
    if has_attribute(func_env, "test_only") {
        return false;
    }
    if targets.is_spec(&func_env.get_qualified_id()) {
        return false;
    }

    true
}

/// Determines the proof status of a function by checking if it has a spec
/// and what verification properties are set.
///
/// Returns:
/// - `Skipped` - Spec is marked to be skipped
/// - `NoProve` - Spec exists but is not marked for verification
/// - `IgnoreAborts` - Spec is verified but ignores abort conditions
/// - `SuccessfulProof` - Spec is verified normally
/// - `NoSpec` - No specification exists for this function
fn determine_spec_status(spec_id: &QualifiedId<FunId>, targets: &PackageTargets) -> ProofStatus {
    if targets.skipped_specs().contains_key(spec_id) {
        ProofStatus::Skipped
    } else if !targets.is_verified_spec(spec_id) {
        ProofStatus::NoProve
    } else if targets.ignores_aborts(spec_id) {
        ProofStatus::IgnoreAborts
    } else {
        ProofStatus::SuccessfulProof
    }
}

fn is_test_module(module_env: &move_model::model::ModuleEnv) -> bool {
    let source_path = module_env.get_source_path();
    source_path
        .to_str()
        .map(|path| path.contains("/tests/") || path.contains("/test/"))
        .unwrap_or(false)
}

fn is_github_dependency(module_env: &move_model::model::ModuleEnv) -> bool {
    let source_path = module_env.get_source_path();
    source_path
        .to_str()
        .map(|path| path.contains("github"))
        .unwrap_or(false)
}

/// Displays statistics for all public and entry functions in the project.
///
/// Shows:
/// - Functions grouped by module
/// - Proof status for each function (has spec, no spec, skipped, etc.)
/// - Summary with total counts
///
/// Excludes:
/// - System/framework modules
/// - Non-public and non-entry functions
/// - Test-only and spec-only functions
pub fn display_function_stats(env: &GlobalEnv, targets: &PackageTargets) {
    println!("📊 Function Statistics\n");

    let excluded_addresses = [
        1u16.into(),      // MoveStdlib
        2u16.into(),      // Sui
        3u16.into(),      // SuiSystem
        0xdee9u16.into(), // DeepBook address
    ];

    let mut total_functions = 0;
    let mut stats_by_status = BTreeMap::new();
    let mut functions_by_module: BTreeMap<String, Vec<_>> = BTreeMap::new();

    for module_env in env.get_modules() {
        let module_addr = module_env.get_name().addr();
        let module_name = module_env
            .get_name()
            .name()
            .display(env.symbol_pool())
            .to_string();

        if excluded_addresses.contains(module_addr)
            || GlobalEnv::SPECS_MODULES_NAMES.contains(&module_name.as_str())
            || is_test_module(&module_env)
            || is_github_dependency(&module_env)
        {
            continue;
        }

        for func_env in module_env.get_functions() {
            if should_include_function(&func_env, targets) {
                let module_name_str = func_env
                    .module_env
                    .get_name()
                    .display(env.symbol_pool())
                    .to_string();
                functions_by_module
                    .entry(module_name_str)
                    .or_default()
                    .push(func_env.get_qualified_id());
            }
        }
    }

    for (module_name, func_ids) in functions_by_module {
        println!("📦 Module: {}", module_name);

        for func_id in func_ids {
            let func_env = env.get_function(func_id);
            total_functions += 1;

            let specs = targets.get_specs(&func_env.get_qualified_id());
            if specs.is_none() {
                *stats_by_status
                    .entry(format!("{}", ProofStatus::NoSpec))
                    .or_insert(0) += 1;
                println!("  {} {}", ProofStatus::NoSpec, func_env.get_name_str());
            } else {
                for spec in specs.unwrap() {
                    let status = determine_spec_status(&spec, targets);
                    *stats_by_status.entry(format!("{}", status)).or_insert(0) += 1;
                    println!("  {} {}", status, func_env.get_name_str());
                }
            }
        }

        println!();
    }

    println!("📈 Summary:");
    println!("Total public/entry functions: {}", total_functions);
    for (status, count) in stats_by_status {
        println!("  {}: {}", status, count);
    }
}
