// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use bimap::btree::BiBTreeMap;
use codespan_reporting::diagnostic::Severity;
use core::fmt;
use std::{
    any::Any,
    collections::{BTreeMap, BTreeSet},
    fmt::Formatter,
    fs,
};

use itertools::{Either, Itertools};
use log::debug;
use move_model::model::{DatatypeId, FunId, FunctionEnv, GlobalEnv, ModuleId, QualifiedId};
use petgraph::graph::DiGraph;

use crate::{
    function_target::{FunctionData, FunctionTarget},
    no_abort_analysis::NoAbortInfo,
    options::ProverOptions,
    package_targets::PackageTargets,
    print_targets_for_test,
    stackless_bytecode_generator::StacklessBytecodeGenerator,
    stackless_control_flow_graph::generate_cfg_in_dot_format,
};

#[derive(Debug, Clone)]
pub enum FunctionHolderTarget {
    All,
    FunctionsAbortCheck,
    SpecNoAbortCheck(ModuleId),
    Function(QualifiedId<FunId>),
    Module(ModuleId),
}

/// A data structure which holds data for multiple function targets, and allows to
/// manipulate them as part of a transformation pipeline.
#[derive(Debug, Clone)]
pub struct FunctionTargetsHolder {
    targets: BTreeMap<QualifiedId<FunId>, BTreeMap<FunctionVariant, FunctionData>>,
    package_targets: PackageTargets,
    function_specs: BiBTreeMap<QualifiedId<FunId>, QualifiedId<FunId>>,
    datatype_invs: BiBTreeMap<QualifiedId<DatatypeId>, QualifiedId<FunId>>,
    target: FunctionHolderTarget,
    prover_options: ProverOptions,
}

/// Describes a function verification flavor.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum VerificationFlavor {
    Regular,
    Instantiated(usize),
    Inconsistency(Box<VerificationFlavor>),
}

impl std::fmt::Display for VerificationFlavor {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationFlavor::Regular => write!(f, ""),
            VerificationFlavor::Instantiated(index) => {
                write!(f, "instantiated_{}", index)
            }
            VerificationFlavor::Inconsistency(flavor) => write!(f, "inconsistency_{}", flavor),
        }
    }
}

/// Describes a function target variant.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FunctionVariant {
    /// The baseline variant which was created from the original Move bytecode and is then
    /// subject of multiple transformations.
    Baseline,
    /// A variant which is instrumented for verification. Only functions which are target
    /// of verification have one of those. There can be multiple verification variants,
    /// each identified by a unique flavor.
    Verification(VerificationFlavor),
}

impl FunctionVariant {
    pub fn is_verified(&self) -> bool {
        matches!(self, FunctionVariant::Verification(..))
    }
}

impl std::fmt::Display for FunctionVariant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use FunctionVariant::*;
        match self {
            Baseline => write!(f, "baseline"),
            Verification(VerificationFlavor::Regular) => write!(f, "verification"),
            Verification(v) => write!(f, "verification[{}]", v),
        }
    }
}

/// A trait describing a function target processor.
pub trait FunctionTargetProcessor {
    /// Processes a function variant. Takes as parameter a target holder which can be mutated, the
    /// env of the function being processed, and the target data. During the time the processor is
    /// called, the target data is removed from the holder, and added back once transformation
    /// has finished. This allows the processor to take ownership on the target data.
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        _fun_env: &FunctionEnv,
        _data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        unimplemented!()
    }

    /// Same as `process` but can return None to indicate that the function variant is
    /// removed. By default, this maps to `Some(self.process(..))`. One needs to implement
    /// either this function or `process`.
    fn process_and_maybe_remove(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> Option<FunctionData> {
        Some(self.process(targets, func_env, data, scc_opt))
    }

    /// Returns a name for this processor. This should be suitable as a file suffix.
    fn name(&self) -> String;

    /// A function which is called once before any `process` call is issued.
    fn initialize(&self, _env: &GlobalEnv, _targets: &mut FunctionTargetsHolder) {}

    /// A function which is called once after the last `process` call.
    fn finalize(&self, _env: &GlobalEnv, _targets: &mut FunctionTargetsHolder) {}

    /// A function which can be implemented to indicate that instead of a sequence of initialize,
    /// process, and finalize, this processor has a single `run` function for the analysis of the
    /// whole set of functions.
    fn is_single_run(&self) -> bool {
        false
    }

    /// To be implemented if `is_single_run()` is true.
    fn run(&self, _env: &GlobalEnv, _targets: &mut FunctionTargetsHolder) {
        unimplemented!()
    }

    /// A function which creates a dump of the processors results, for debugging.
    fn dump_result(
        &self,
        _f: &mut Formatter<'_>,
        _env: &GlobalEnv,
        _targets: &FunctionTargetsHolder,
    ) -> fmt::Result {
        Ok(())
    }
}

pub struct ProcessorResultDisplay<'a> {
    pub env: &'a GlobalEnv,
    pub targets: &'a FunctionTargetsHolder,
    pub processor: &'a dyn FunctionTargetProcessor,
}

impl fmt::Display for ProcessorResultDisplay<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.processor.dump_result(f, self.env, self.targets)
    }
}

/// A processing pipeline for function targets.
#[derive(Default)]
pub struct FunctionTargetPipeline {
    processors: Vec<Box<dyn FunctionTargetProcessor>>,
}

impl FunctionTargetsHolder {
    pub fn new(
        prover_options: ProverOptions,
        package_targets: &PackageTargets,
        target: FunctionHolderTarget,
    ) -> Self {
        Self {
            targets: BTreeMap::new(),
            function_specs: BiBTreeMap::new(),
            datatype_invs: BiBTreeMap::new(),
            prover_options,
            target,
            package_targets: package_targets.clone(),
        }
    }

    pub fn new_dummy(&self) -> Self {
        Self::new(
            self.prover_options.clone(),
            &self.package_targets,
            self.target.clone(),
        )
    }

    pub fn prover_options(&self) -> &ProverOptions {
        &self.prover_options
    }

    pub fn func_abort_check_mode(&self) -> bool {
        matches!(self.target, FunctionHolderTarget::FunctionsAbortCheck)
    }

    pub fn spec_no_abort_check_mode(&self) -> bool {
        matches!(self.target, FunctionHolderTarget::SpecNoAbortCheck(..))
    }

    /// Get an iterator for all functions this holder.
    pub fn get_funs(&self) -> impl Iterator<Item = QualifiedId<FunId>> + '_ {
        self.targets.keys().cloned()
    }

    /// Gets an iterator for all functions and variants in this holder.
    pub fn get_funs_and_variants(
        &self,
    ) -> impl Iterator<Item = (QualifiedId<FunId>, FunctionVariant)> + '_ {
        self.targets
            .iter()
            .flat_map(|(id, vs)| vs.keys().map(move |v| (*id, v.clone())))
    }

    pub fn get_fun_by_spec(&self, id: &QualifiedId<FunId>) -> Option<&QualifiedId<FunId>> {
        self.function_specs.get_by_left(id)
    }

    pub fn get_spec_by_fun(&self, id: &QualifiedId<FunId>) -> Option<&QualifiedId<FunId>> {
        self.function_specs.get_by_right(id)
    }

    fn in_target(&self, id: &QualifiedId<FunId>) -> bool {
        match self.target {
            FunctionHolderTarget::All => true,
            FunctionHolderTarget::FunctionsAbortCheck => {
                self.package_targets.abort_check_functions().contains(id)
            }
            FunctionHolderTarget::SpecNoAbortCheck(mid) => {
                id.module_id == mid && self.package_targets.no_verify_specs().contains(id)
            }
            FunctionHolderTarget::Function(qid) => id == &qid,
            FunctionHolderTarget::Module(mid) => id.module_id == mid,
        }
    }

    pub fn no_verify_specs(&self) -> Box<dyn Iterator<Item = &QualifiedId<FunId>> + '_> {
        // Return specs that should not be verified: either explicitly marked as no-verify,
        // or not in the current target scope
        Box::new(
            self.specs().filter(|s| {
                self.package_targets.no_verify_specs().contains(s) || !self.in_target(s)
            }),
        )
    }

    pub fn ignore_aborts(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.package_targets.ignore_aborts()
    }

    pub fn scenario_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.package_targets.scenario_specs()
    }

    pub fn ignores_aborts(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.ignore_aborts().contains(id)
    }

    pub fn is_abort_check_fun(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.abort_check_functions().contains(id)
    }

    pub fn is_function_with_abort_check(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.abort_check_functions().contains(id)
            || self.package_targets.pure_functions().contains(id)
    }

    pub fn should_generate_abort_check(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets
            .target_no_abort_check_functions()
            .contains(id)
            && !self
                .get_annotation::<NoAbortInfo>(id, &FunctionVariant::Baseline)
                .does_not_abort
    }

    pub fn target_no_abort_check_functions(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets
            .target_no_abort_check_functions()
            .contains(id)
    }

    pub fn is_pure_fun(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.pure_functions().contains(id)
    }

    pub fn is_axiom_fun(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.axiom_functions().contains(id)
    }

    pub fn axiom_functions(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.package_targets.axiom_functions()
    }

    pub fn is_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.get_fun_by_spec(id).is_some() || self.package_targets.scenario_specs().contains(id)
    }

    pub fn is_function_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.get_fun_by_spec(id).is_some()
    }

    pub fn is_verified_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.is_spec(id) && !self.no_verify_specs().contains(id)
    }

    pub fn is_scenario_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.scenario_specs().contains(id)
    }

    pub fn omits_opaque(&self, id: &QualifiedId<FunId>) -> bool {
        self.package_targets.omit_opaque_specs().contains(id)
    }

    pub fn specs(&self) -> impl Iterator<Item = &QualifiedId<FunId>> {
        self.function_specs
            .left_values()
            .chain(self.package_targets.scenario_specs().iter())
    }

    pub fn specs_with_target(&self) -> impl Iterator<Item = QualifiedId<FunId>> + '_ {
        self.specs()
            .filter(|spec_id| self.targets.get(spec_id).is_some())
            .cloned()
    }

    pub fn get_inv_by_datatype(&self, id: &QualifiedId<DatatypeId>) -> Option<&QualifiedId<FunId>> {
        self.datatype_invs.get_by_left(id)
    }

    pub fn get_datatype_by_inv(&self, id: &QualifiedId<FunId>) -> Option<&QualifiedId<DatatypeId>> {
        self.datatype_invs.get_by_right(id)
    }

    pub fn get_datatype_invs(&self) -> &BiBTreeMap<QualifiedId<DatatypeId>, QualifiedId<FunId>> {
        &self.datatype_invs
    }

    pub fn get_spec_boogie_options(&self, id: &QualifiedId<FunId>) -> Option<&String> {
        self.package_targets.spec_boogie_options().get(id)
    }

    pub fn get_spec_timeout(&self, id: &QualifiedId<FunId>) -> Option<&u64> {
        self.package_targets.spec_timeouts().get(id)
    }

    pub fn get_loop_invariants(
        &self,
        id: &QualifiedId<FunId>,
    ) -> Option<&BiBTreeMap<QualifiedId<FunId>, usize>> {
        self.package_targets.loop_invariants().get(id)
    }

    pub fn get_uninterpreted_functions(
        &self,
        spec_id: &QualifiedId<FunId>,
    ) -> Option<&BTreeSet<QualifiedId<FunId>>> {
        self.package_targets.get_uninterpreted_functions(spec_id)
    }

    pub fn is_uninterpreted_for_spec(
        &self,
        spec_id: &QualifiedId<FunId>,
        callee_id: &QualifiedId<FunId>,
    ) -> bool {
        self.package_targets
            .is_uninterpreted_for_spec(spec_id, callee_id)
    }

    fn has_extra_bpl(&self, env: &GlobalEnv, mid: &ModuleId) -> bool {
        if self.package_targets.get_module_extra_bpl(mid).is_some() {
            return true;
        }
        for fun in env.get_module(*mid).get_functions() {
            if self
                .package_targets
                .get_function_extra_bpl(&fun.get_qualified_id())
                .is_some()
            {
                return true;
            }
        }
        false
    }

    pub fn has_targeted_extra_bpl(&self, env: &GlobalEnv) -> bool {
        match self.target {
            FunctionHolderTarget::All => self.package_targets.prelude_extra_exists(),
            FunctionHolderTarget::FunctionsAbortCheck => {
                self.package_targets.prelude_extra_exists()
            }
            FunctionHolderTarget::SpecNoAbortCheck(mid) => self.has_extra_bpl(env, &mid),
            FunctionHolderTarget::Function(qid) => {
                self.package_targets.get_function_extra_bpl(&qid).is_some()
                    || self
                        .package_targets
                        .get_module_extra_bpl(&qid.module_id)
                        .is_some()
            }
            FunctionHolderTarget::Module(mid) => self.has_extra_bpl(env, &mid),
        }
    }

    // Checks if a function is marked as uninterpreted by all verified specs.
    pub fn is_uninterpreted(&self, func_id: &QualifiedId<FunId>) -> bool {
        let verified_specs: Vec<_> = self
            .specs()
            .filter(|spec_id| self.is_verified_spec(spec_id))
            .collect();

        // If no verified specs, function is not uninterpreted
        if verified_specs.is_empty() {
            return false;
        }

        // Check if ALL verified specs mark this function as uninterpreted
        verified_specs.iter().all(|spec_id| {
            self.package_targets
                .is_uninterpreted_for_spec(spec_id, func_id)
        })
    }

    pub fn get_loop_inv_with_targets(
        &self,
    ) -> BiBTreeMap<QualifiedId<FunId>, BTreeSet<QualifiedId<FunId>>> {
        self.package_targets
            .loop_invariants()
            .iter()
            .map(|(target_fun_id, invs)| {
                (
                    target_fun_id.clone(),
                    invs.iter().map(|el| el.0.clone()).collect(),
                )
            })
            .collect()
    }

    /// Return the specification of the callee function if the specification can
    /// be used instead of the callee by the caller. This is the case if and
    /// only if
    /// * a specification exists for the callee, and
    /// * the caller is not the specification.
    pub fn get_callee_spec_qid(
        &self,
        caller_qid: &QualifiedId<FunId>,
        callee_qid: &QualifiedId<FunId>,
    ) -> Option<&QualifiedId<FunId>> {
        match self.get_spec_by_fun(callee_qid) {
            Some(spec_qid) if spec_qid != caller_qid => Some(spec_qid),
            _ => None,
        }
    }

    /// Adds a new function target. The target will be initialized from the Move byte code.
    pub fn add_target(&mut self, func_env: &FunctionEnv<'_>) {
        let generator = StacklessBytecodeGenerator::new(func_env);
        let data = generator.generate_function();
        self.targets
            .entry(func_env.get_qualified_id())
            .or_default()
            .insert(FunctionVariant::Baseline, data);

        if let Some(spec) = self
            .package_targets
            .find_target_spec(&func_env.get_qualified_id())
        {
            self.process_spec(func_env, &spec);
        }

        if let Some(datatype_id) = self
            .package_targets
            .find_datatype_inv(&func_env.get_qualified_id())
        {
            self.process_inv(func_env, &datatype_id);
        }
    }

    fn process_spec(&mut self, spec_env: &FunctionEnv, target_id: &QualifiedId<FunId>) {
        let env = spec_env.module_env.env;

        if matches!(self.target, FunctionHolderTarget::FunctionsAbortCheck) {
            if !self
                .package_targets
                .is_system_spec(&spec_env.get_qualified_id())
            {
                return;
            }
        } else if matches!(self.target, FunctionHolderTarget::All) {
            // pass
        } else {
            let (is_related, target_module) = match self.target {
                FunctionHolderTarget::Function(qid) => (
                    self.package_targets.is_belongs_to_module_explicit_specs(
                        &env.get_module(qid.module_id),
                        spec_env.get_qualified_id(),
                    ) || self.package_targets.is_belongs_to_function_explicit_specs(
                        &env.get_function(qid),
                        spec_env.get_qualified_id(),
                    ),
                    qid.module_id,
                ),
                FunctionHolderTarget::Module(mid) | FunctionHolderTarget::SpecNoAbortCheck(mid) => {
                    (
                        self.package_targets.is_belongs_to_module_explicit_specs(
                            &env.get_module(mid),
                            spec_env.get_qualified_id(),
                        ),
                        mid,
                    )
                }
                FunctionHolderTarget::FunctionsAbortCheck | FunctionHolderTarget::All => {
                    unreachable!()
                }
            };

            if spec_env.module_env.get_id() != target_module
                && !is_related
                && !self
                    .package_targets
                    .is_system_spec(&spec_env.get_qualified_id())
            {
                return;
            }
        }

        if let Some(qid) = self.function_specs.get_by_right(&target_id) {
            if !self.package_targets.is_system_spec(qid) {
                if self
                    .package_targets
                    .is_system_spec(&spec_env.get_qualified_id())
                {
                    return;
                }
                env.diag(
                    Severity::Error,
                    &spec_env.get_loc(),
                    &format!(
                        "Duplicate target function: {}",
                        env.get_function(*target_id).get_name_str()
                    ),
                );
                return;
            }
        }

        self.function_specs
            .insert(spec_env.get_qualified_id(), *target_id);
    }

    fn process_inv(&mut self, func_env: &FunctionEnv, sid: &QualifiedId<DatatypeId>) {
        if self.datatype_invs.contains_left(sid) {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                &format!(
                    "Duplicate invariant declaration for struct: {}",
                    func_env
                        .module_env
                        .env
                        .get_struct(*sid)
                        .get_name()
                        .display(func_env.module_env.env.symbol_pool()),
                ),
            );
        } else {
            self.datatype_invs
                .insert(sid.clone(), func_env.get_qualified_id());
        }
    }

    /// Gets a function target for read-only consumption, for the given variant.
    pub fn get_target<'env>(
        &'env self,
        func_env: &'env FunctionEnv<'env>,
        variant: &FunctionVariant,
    ) -> FunctionTarget<'env> {
        self.get_target_opt(func_env, variant).expect(&format!(
            "expected function target: {} ({:?})",
            func_env.get_full_name_str(),
            variant
        ))
    }

    pub fn get_target_opt<'env>(
        &'env self,
        func_env: &'env FunctionEnv<'env>,
        variant: &FunctionVariant,
    ) -> Option<FunctionTarget<'env>> {
        self.get_data(&func_env.get_qualified_id(), variant)
            .map(|data| FunctionTarget::new(func_env, data))
    }

    pub fn has_target(&self, func_env: &FunctionEnv<'_>, variant: &FunctionVariant) -> bool {
        self.get_data(&func_env.get_qualified_id(), variant)
            .is_some()
    }

    /// Gets all available variants for function.
    pub fn get_target_variants(&self, func_env: &FunctionEnv<'_>) -> Vec<FunctionVariant> {
        self.targets
            .get(&func_env.get_qualified_id())
            .map(|vs| vs.keys().cloned().collect_vec())
            .unwrap_or_default()
    }

    /// Gets targets for all available variants.
    pub fn get_targets<'env>(
        &'env self,
        func_env: &'env FunctionEnv<'env>,
    ) -> Vec<(FunctionVariant, FunctionTarget<'env>)> {
        self.targets
            .get(&func_env.get_qualified_id())
            .map(|vs| {
                vs.iter()
                    .map(|(v, d)| (v.clone(), FunctionTarget::new(func_env, d)))
                    .collect_vec()
            })
            .unwrap_or_default()
    }

    /// Gets function data for a variant.
    pub fn get_data(
        &self,
        id: &QualifiedId<FunId>,
        variant: &FunctionVariant,
    ) -> Option<&FunctionData> {
        self.targets.get(id).and_then(|vs| vs.get(variant))
    }

    /// Gets mutable function data for a variant.
    pub fn get_data_mut(
        &mut self,
        id: &QualifiedId<FunId>,
        variant: &FunctionVariant,
    ) -> Option<&mut FunctionData> {
        self.targets.get_mut(id).and_then(|vs| vs.get_mut(variant))
    }

    /// Removes function data for a variant.
    pub fn remove_target_data(
        &mut self,
        id: &QualifiedId<FunId>,
        variant: &FunctionVariant,
    ) -> FunctionData {
        self.targets
            .get_mut(id)
            .expect("function target exists")
            .remove(variant)
            .expect("variant exists")
    }

    /// Remove all variants of a function from targets
    pub fn remove_target(&mut self, id: &QualifiedId<FunId>) {
        self.targets.remove(id);
    }

    /// Sets function data for a function's variant.
    pub fn insert_target_data(
        &mut self,
        id: &QualifiedId<FunId>,
        variant: FunctionVariant,
        data: FunctionData,
    ) {
        self.targets
            .get_mut(id)
            .expect(&format!(
                "function qualified id {:#?} not found in targets",
                id
            ))
            .insert(variant, data);
    }

    pub fn get_annotation<T: Any>(&self, id: &QualifiedId<FunId>, variant: &FunctionVariant) -> &T {
        self.get_data(id, variant)
            .expect("function data not found")
            .annotations
            .get::<T>()
            .expect(&format!(
                "annotation {} not found",
                std::any::type_name::<T>()
            ))
    }

    /// Processes the function target data for given function.
    fn process(
        &mut self,
        func_env: &FunctionEnv,
        processor: &dyn FunctionTargetProcessor,
        scc_opt: Option<&[FunctionEnv]>,
    ) {
        // Check if this function exists in targets before processing
        if !self.targets.contains_key(&func_env.get_qualified_id()) {
            // Function was removed from targets, skip processing
            return;
        }

        for variant in self.get_target_variants(func_env) {
            // Remove data so we can own it.
            let data = self.remove_target_data(&func_env.get_qualified_id(), &variant);
            if let Some(processed_data) =
                processor.process_and_maybe_remove(self, func_env, data, scc_opt)
            {
                // Put back processed data.
                self.insert_target_data(&func_env.get_qualified_id(), variant, processed_data);
            }
        }
    }

    pub fn dump_spec_info(&self, env: &GlobalEnv, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "=== function target holder ===")?;
        writeln!(f)?;
        writeln!(f, "Verification specs:")?;
        for spec in self.specs() {
            let fun_env = env.get_function(*spec);
            if self.is_verified_spec(spec)
                && self.has_target(
                    &fun_env,
                    &FunctionVariant::Verification(VerificationFlavor::Regular),
                )
            {
                writeln!(f, "  {}", fun_env.get_full_name_str())?;
            }
        }
        writeln!(f, "Opaque specs:")?;
        for (spec, fun) in self.function_specs.iter() {
            writeln!(
                f,
                "  {} -> {}",
                env.get_function(*spec).get_full_name_str(),
                env.get_function(*fun).get_full_name_str()
            )?;
        }
        writeln!(f, "No verify specs:")?;
        for spec in self.no_verify_specs() {
            writeln!(f, "  {}", env.get_function(*spec).get_full_name_str())?;
        }
        writeln!(f, "No asserts specs:")?;
        for spec in self.ignore_aborts() {
            writeln!(f, "  {}", env.get_function(*spec).get_full_name_str())?;
        }
        writeln!(f, "Scenario specs:")?;
        for spec in self.scenario_specs() {
            writeln!(f, "  {}", env.get_function(*spec).get_full_name_str())?;
        }
        writeln!(f, "Datatype invariants:")?;
        for (datatype, inv) in self.datatype_invs.iter() {
            writeln!(
                f,
                "  {} -> {}",
                env.get_struct(*datatype).get_full_name_str(),
                env.get_function(*inv).get_full_name_str(),
            )?;
        }
        Ok(())
    }
}

pub struct FunctionTargetsHolderDisplay<'a> {
    pub targets: &'a FunctionTargetsHolder,
    pub env: &'a GlobalEnv,
}

impl<'a> fmt::Display for FunctionTargetsHolderDisplay<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.targets.dump_spec_info(self.env, f)
    }
}

impl FunctionTargetPipeline {
    /// Adds a processor to this pipeline. Processor will be called in the order they have been
    /// added.
    pub fn add_processor(&mut self, processor: Box<dyn FunctionTargetProcessor>) {
        self.processors.push(processor)
    }

    /// Gets the last processor in the pipeline, for testing.
    pub fn last_processor(&self) -> &dyn FunctionTargetProcessor {
        self.processors
            .iter()
            .last()
            .expect("pipeline not empty")
            .as_ref()
    }

    /// Build the call graph
    pub fn build_call_graph(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> DiGraph<QualifiedId<FunId>, ()> {
        let mut graph = DiGraph::new();
        let mut nodes = BTreeMap::new();
        for fun_id in targets.get_funs() {
            let node_idx = graph.add_node(fun_id);
            nodes.insert(fun_id, node_idx);
        }
        for fun_id in targets.get_funs() {
            let src_idx = nodes.get(&fun_id).unwrap();
            let fun_env = env.get_function(fun_id);
            for callee in fun_env.get_called_functions() {
                // add edge to original callee if it exists in targets
                if let Some(dst_idx) = nodes.get(&callee) {
                    graph.add_edge(*src_idx, *dst_idx, ());
                }

                // add edge to spec callee if it's different and exists in targets
                if let Some(spec_qid) =
                    targets.get_callee_spec_qid(&fun_env.get_qualified_id(), &callee)
                {
                    if let Some(dst_idx) = nodes.get(spec_qid) {
                        graph.add_edge(*src_idx, *dst_idx, ());
                    }
                }
            }
        }
        graph
    }

    /// Sort the call graph in topological order with strongly connected components (SCCs)
    /// to represent recursive calls.
    pub fn sort_targets_in_topological_order(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> Vec<Either<QualifiedId<FunId>, Vec<QualifiedId<FunId>>>> {
        let graph = Self::build_call_graph(env, targets);
        let sccs = petgraph::algo::kosaraju_scc(&graph);
        sccs.iter()
            .map(|scc| scc.iter().map(|node_idx| graph[*node_idx]).collect_vec())
            .map(|scc| {
                if scc.len() == 1 {
                    // single node, no cycle
                    Either::Left(scc[0])
                } else {
                    // multiple nodes, a strongly connected component
                    Either::Right(scc)
                }
            })
            .collect_vec()
    }

    /// Runs the pipeline on all functions in the targets holder. Processors are run on each
    /// individual function in breadth-first fashion; i.e. a processor can expect that processors
    /// preceding it in the pipeline have been executed for all functions before it is called.
    pub fn run_with_hook<H1, H2>(
        &self,
        env: &GlobalEnv,
        targets: &mut FunctionTargetsHolder,
        hook_before_pipeline: H1,
        hook_after_each_processor: H2,
    ) -> Result<(), &Box<dyn FunctionTargetProcessor>>
    where
        H1: Fn(&FunctionTargetsHolder),
        H2: Fn(usize, &dyn FunctionTargetProcessor, &FunctionTargetsHolder),
    {
        hook_before_pipeline(targets);
        for (step_count, processor) in self.processors.iter().enumerate() {
            let topological_order: Vec<Either<QualifiedId<FunId>, Vec<QualifiedId<FunId>>>> =
                Self::sort_targets_in_topological_order(env, targets);
            if processor.is_single_run() {
                processor.run(env, targets);
            } else {
                processor.initialize(env, targets);
                for item in &topological_order {
                    match item {
                        Either::Left(fid) => {
                            let func_env = env.get_function(*fid);
                            targets.process(&func_env, processor.as_ref(), None);
                        }
                        Either::Right(scc) => 'fixedpoint: loop {
                            let scc_env: Vec<_> =
                                scc.iter().map(|fid| env.get_function(*fid)).collect();
                            for fid in scc {
                                let func_env = env.get_function(*fid);
                                targets.process(&func_env, processor.as_ref(), Some(&scc_env));
                            }

                            // check for fixedpoint in summaries
                            for fid in scc {
                                let func_env = env.get_function(*fid);
                                for (_, target) in targets.get_targets(&func_env) {
                                    if !target.data.annotations.reached_fixedpoint() {
                                        continue 'fixedpoint;
                                    }
                                }
                            }
                            // fixedpoint reached when execution hits this line
                            break 'fixedpoint;
                        },
                    }
                }
                processor.finalize(env, targets);
            }
            hook_after_each_processor(step_count + 1, processor.as_ref(), targets);
            if env.has_errors() {
                return Err(processor);
            }
        }
        Ok(())
    }

    /// Run the pipeline on all functions in the targets holder, with no hooks in effect
    pub fn run(
        &self,
        env: &GlobalEnv,
        targets: &mut FunctionTargetsHolder,
    ) -> Result<(), &Box<dyn FunctionTargetProcessor>> {
        self.run_with_hook(env, targets, |_| {}, |_, _, _| {})
    }

    /// Runs the pipeline on all functions in the targets holder, dump the bytecode before the
    /// pipeline as well as after each processor pass. If `dump_cfg` is set, dump the per-function
    /// control-flow graph (in dot format) too.
    pub fn run_with_dump(
        &self,
        env: &GlobalEnv,
        targets: &mut FunctionTargetsHolder,
        dump_base_name: &str,
        dump_cfg: bool,
    ) -> Result<(), &Box<dyn FunctionTargetProcessor>> {
        self.run_with_hook(
            env,
            targets,
            |holders| {
                Self::dump_to_file(
                    dump_base_name,
                    0,
                    "stackless",
                    &Self::get_pre_pipeline_dump(env, holders),
                )
            },
            |step_count, processor, holders| {
                let suffix = processor.name();
                Self::dump_to_file(
                    dump_base_name,
                    step_count,
                    &suffix,
                    &Self::get_per_processor_dump(env, holders, processor),
                );
                if dump_cfg {
                    Self::dump_cfg(env, holders, dump_base_name, step_count, &suffix);
                }
            },
        )
    }

    fn print_targets(env: &GlobalEnv, name: &str, targets: &FunctionTargetsHolder) -> String {
        print_targets_for_test(env, &format!("after processor `{}`", name), targets)
    }

    fn get_pre_pipeline_dump(env: &GlobalEnv, targets: &FunctionTargetsHolder) -> String {
        Self::print_targets(env, "stackless", targets)
    }

    fn get_per_processor_dump(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        processor: &dyn FunctionTargetProcessor,
    ) -> String {
        let mut dump = format!(
            "{}",
            ProcessorResultDisplay {
                env,
                targets,
                processor,
            }
        );
        if !processor.is_single_run() {
            if !dump.is_empty() {
                dump = format!("\n\n{}", dump);
            }
            dump.push_str(&Self::print_targets(env, &processor.name(), targets));
        }
        dump
    }

    fn dump_to_file(base_name: &str, step_count: usize, suffix: &str, content: &str) {
        let dump = format!("{}\n", content.trim());
        let file_name = format!("{}_{}_{}.bytecode", base_name, step_count, suffix);
        debug!("dumping bytecode to `{}`", file_name);
        fs::write(&file_name, dump).expect("dumping bytecode");
    }

    /// Generate dot files for control-flow graphs.
    fn dump_cfg(
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        base_name: &str,
        step_count: usize,
        suffix: &str,
    ) {
        for (fun_id, variants) in &targets.targets {
            let func_env = env.get_function(*fun_id);
            let func_name = func_env.get_full_name_str();
            let func_name = func_name.replace("::", "__");
            for (variant, data) in variants {
                if !data.code.is_empty() {
                    let dot_file = format!(
                        "{}_{}_{}_{}_{}_cfg.dot",
                        base_name, step_count, suffix, func_name, variant
                    );
                    debug!("generating dot graph for cfg in `{}`", dot_file);
                    let func_target = FunctionTarget::new(&func_env, data);
                    let dot_graph = generate_cfg_in_dot_format(&func_target);
                    fs::write(&dot_file, &dot_graph).expect("generating dot file for CFG");
                }
            }
        }
    }
}
