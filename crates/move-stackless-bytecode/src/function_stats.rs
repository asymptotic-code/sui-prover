use crate::function_target_pipeline::FunctionTargetsHolder;
use move_binary_format::file_format::Visibility;
use move_model::{
    ast::Attribute,
    model::{FunctionEnv, GlobalEnv},
};
use std::collections::{BTreeMap, BTreeSet};

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
/// - Non-public functions
/// - Functions with `spec_only` attribute
/// - Functions with `test_only` attribute
/// - Spec functions themselves
fn should_include_function(func_env: &FunctionEnv, targets: &FunctionTargetsHolder) -> bool {
    let func_id = func_env.get_qualified_id();

    if func_env.visibility() != Visibility::Public {
        return false;
    }
    if has_attribute(func_env, "spec_only") {
        return false;
    }
    if has_attribute(func_env, "test_only") {
        return false;
    }
    if targets.is_spec(&func_id) {
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
fn determine_spec_status(func_env: &FunctionEnv, targets: &FunctionTargetsHolder) -> ProofStatus {
    let func_id = func_env.get_qualified_id();
    let skip_specs_set: BTreeSet<_> = targets.skip_specs().collect();

    if let Some(spec_id) = targets.get_spec_by_fun(&func_id) {
        if skip_specs_set.contains(&spec_id) {
            ProofStatus::Skipped
        } else if !targets.is_verified_spec(spec_id) {
            ProofStatus::NoProve
        } else if targets.ignores_aborts(spec_id) {
            ProofStatus::IgnoreAborts
        } else {
            ProofStatus::SuccessfulProof
        }
    } else {
        ProofStatus::NoSpec
    }
}

/// Displays statistics for all public functions in the project.
///
/// Shows:
/// - Functions grouped by module
/// - Proof status for each function (has spec, no spec, skipped, etc.)
/// - Summary with total counts
///
/// Excludes:
/// - System/framework modules
/// - Non-public functions
/// - Test-only and spec-only functions
pub fn display_function_stats(env: &GlobalEnv, targets: &FunctionTargetsHolder) {
    println!("📊 Function Statistics\n");

    let excluded_addresses = [
        0u16.into(),      // System address (core framework)
        1u16.into(),      // Tests address
        2u16.into(),      // Event address
        3u16.into(),      // Stdlib address
        0xdee9u16.into(), // DeepBook address
    ];

    let mut total_public_functions = 0;
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
            total_public_functions += 1;

            let status = determine_spec_status(&func_env, targets);
            *stats_by_status.entry(format!("{}", status)).or_insert(0) += 1;

            println!("  {} {}", status, func_env.get_name_str());
        }

        println!();
    }

    println!("📈 Summary:");
    println!("Total public functions: {}", total_public_functions);
    for (status, count) in stats_by_status {
        println!("  {}: {}", status, count);
    }
}
