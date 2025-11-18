use crate::target_filter::TargetFilterOptions;
use move_binary_format::file_format::Visibility;
use move_compiler::shared::known_attributes::{
    AttributeKind_, ExternalAttribute, KnownAttribute, VerificationAttribute,
};
use move_model::{
    ast::Attribute,
    model::{FunId, FunctionEnv, GlobalEnv, ModuleId, QualifiedId},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofStatus {
    Skipped(String),
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
            ProofStatus::Skipped(reason) => write!(f, "⏭️  skipped spec: {}", reason),
            ProofStatus::NoProve => write!(f, "✖️ no prove"),
            ProofStatus::NoSpec => write!(f, "❌ no spec"),
        }
    }
}

pub struct CollectedTargets {
    pub target_specs: BTreeSet<QualifiedId<FunId>>,
    pub target_modules: BTreeSet<ModuleId>,
    pub no_verify_specs: BTreeSet<QualifiedId<FunId>>,
    pub no_verify_modules: BTreeSet<ModuleId>,
    pub abort_checks: BTreeSet<QualifiedId<FunId>>,
    pub skipped_specs: BTreeMap<QualifiedId<FunId>, String>,
    pub ignore_abort_specs: BTreeSet<QualifiedId<FunId>>,
}

impl CollectedTargets {
    pub fn new(env: &GlobalEnv, filter: TargetFilterOptions) -> Self {
        let mut s = Self {
            target_specs: BTreeSet::new(),
            target_modules: BTreeSet::new(),
            abort_checks: BTreeSet::new(),
            skipped_specs: BTreeMap::new(),
            no_verify_specs: BTreeSet::new(),
            ignore_abort_specs: BTreeSet::new(),
            no_verify_modules: BTreeSet::new(),
        };
        s.collect_targets(env, filter);
        s
    }

    fn collect_targets(&mut self, env: &GlobalEnv, filter: TargetFilterOptions) {
        for module_env in env.get_modules() {
            if module_env.is_target() {
                for func_env in module_env.get_functions() {
                    self.check_spec_scope(&func_env, filter.clone());
                    self.check_abort_check_scope(&func_env, filter.clone());
                }
            }
        }
    }

    fn check_spec_scope(&mut self, func_env: &FunctionEnv, filter: TargetFilterOptions) {
        if let Some(KnownAttribute::Verification(VerificationAttribute::Spec {
            focus,
            prove,
            skip,
            target: _,
            no_opaque: _,
            ignore_abort,
            boogie_opt: _,
            timeout: _,
        })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::Spec)
            .map(|attr| &attr.value)
        {
            if filter.is_targeted(func_env) {
                if *ignore_abort {
                    self.ignore_abort_specs.insert(func_env.get_qualified_id());
                }
                if let Some(str) = skip {
                    self.skipped_specs.insert(func_env.get_qualified_id(), str.to_string());
                    self.no_verify_specs.insert(func_env.get_qualified_id());
                    self.no_verify_modules.insert(func_env.module_env.get_id());
                    return;
                }
                if *focus || *prove {
                    self.target_specs.insert(func_env.get_qualified_id());
                    self.target_modules.insert(func_env.module_env.get_id());
                } else {
                    self.no_verify_specs.insert(func_env.get_qualified_id());
                    self.no_verify_modules.insert(func_env.module_env.get_id());
                }
            }
        }
    }

    fn check_abort_check_scope(&mut self, func_env: &FunctionEnv, filter: TargetFilterOptions) -> bool {
        if let Some(KnownAttribute::External(ExternalAttribute { attrs })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::External)
            .map(|attr| &attr.value)
        {
            if filter.is_targeted(func_env)
                && attrs
                    .into_iter()
                    .any(|attr| attr.2.value.name().value.as_str() == "no_abort".to_string())
            {
               self.abort_checks.insert(func_env.get_qualified_id());
            }
        }

        false
    }

    fn is_spec(&self, func_id: &QualifiedId<FunId>) -> bool {
        self.target_specs.contains(func_id) || self.no_verify_specs.contains(func_id)
    }

    pub fn has_specs(&self) -> bool {
        !self.target_specs.is_empty() || !self.no_verify_specs.is_empty()
    }

    pub fn ignores_aborts(&self, func_id: &QualifiedId<FunId>) -> bool {
        self.ignore_abort_specs.contains(func_id)
    }

    pub fn is_verified_spec(&self, func_id: &QualifiedId<FunId>) -> bool {
        self.target_specs.contains(func_id)
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
fn should_include_function(func_env: &FunctionEnv, targets: &CollectedTargets) -> bool {
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
fn determine_spec_status(func_env: &FunctionEnv, targets: &CollectedTargets) -> ProofStatus {
    let func_id = func_env.get_qualified_id();

    if let Some(spec_id) = Some(&func_env.get_qualified_id()) {// targets.get_spec_by_fun(&func_id) { // TODO
        if let Some(reason) = targets.skipped_specs.get(spec_id) {
            ProofStatus::Skipped(reason.to_string())
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
pub fn display_function_stats(env: &GlobalEnv, targets: &CollectedTargets) {
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
