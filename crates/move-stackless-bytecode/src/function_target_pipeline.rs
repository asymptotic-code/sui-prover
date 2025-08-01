// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use bimap::btree::BiBTreeMap;
use codespan_reporting::diagnostic::Severity;
use move_binary_format::file_format::FunctionHandleIndex;
use core::fmt;
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Formatter,
    fs,
};

use itertools::{Either, Itertools};
use log::debug;
use petgraph::graph::DiGraph;

use move_compiler::{
    expansion::ast::{ModuleAccess, ModuleAccess_}, shared::{
        known_attributes::{AttributeKind_, KnownAttribute, VerificationAttribute},
    }
};

use move_model::{
    ast::ModuleName,
    model::{DatatypeId, FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId, QualifiedId},
};

use crate::{
    function_target::{FunctionData, FunctionTarget},
    print_targets_for_test,
    stackless_bytecode_generator::StacklessBytecodeGenerator,
    stackless_control_flow_graph::generate_cfg_in_dot_format,
};

/// A data structure which holds data for multiple function targets, and allows to
/// manipulate them as part of a transformation pipeline.
#[derive(Debug, Clone)]
pub struct FunctionTargetsHolder {
    targets: BTreeMap<QualifiedId<FunId>, BTreeMap<FunctionVariant, FunctionData>>,
    function_specs: BiBTreeMap<QualifiedId<FunId>, QualifiedId<FunId>>,
    no_verify_specs: BTreeSet<QualifiedId<FunId>>,
    no_focus_specs: BTreeSet<QualifiedId<FunId>>,
    omit_opaque_specs: BTreeSet<QualifiedId<FunId>>,
    skip_specs: BTreeMap<QualifiedId<FunId>, String>,
    focus_specs: BTreeSet<QualifiedId<FunId>>,
    ignore_aborts: BTreeSet<QualifiedId<FunId>>,
    scenario_specs: BTreeSet<QualifiedId<FunId>>,
    datatype_invs: BiBTreeMap<QualifiedId<DatatypeId>, QualifiedId<FunId>>,
    target_modules: BTreeSet<ModuleId>,
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
    pub fn new() -> Self {
        Self {
            targets: BTreeMap::new(),
            function_specs: BiBTreeMap::new(),
            no_verify_specs: BTreeSet::new(),
            no_focus_specs: BTreeSet::new(),
            omit_opaque_specs: BTreeSet::new(),
            skip_specs: BTreeMap::new(),
            focus_specs: BTreeSet::new(),
            ignore_aborts: BTreeSet::new(),
            scenario_specs: BTreeSet::new(),
            datatype_invs: BiBTreeMap::new(),
            target_modules: BTreeSet::new(),
        }
    }

    /// Counts system specs dynamically based on their module addresses.
    /// System specs are those from modules deployed at address 0x0:
    /// - specs::* modules (sui-framework-specs package)
    /// - prover::* modules (prover package)
    fn count_system_specs(&self, env: &GlobalEnv) -> usize {
        let mut system_specs_count = 0;
        let system_address = &0u16.into(); // Address 0x0 used by system modules

        // Count function specs from system modules
        for spec_id in self.function_specs.left_values().chain(self.scenario_specs.iter()) {
            let func_env = env.get_function(*spec_id);
            let module_env = &func_env.module_env;
            if module_env.get_name().addr() == system_address {
                let module_name = module_env.get_name().name().display(env.symbol_pool()).to_string();
                if GlobalEnv::SPECS_MODULES_NAMES.contains(&module_name.as_str()) {
                    system_specs_count += 1;
                }
            }
        }

        system_specs_count
    }

    pub fn for_one_spec(target: &QualifiedId<FunId>, instance: FunctionTargetsHolder) -> Self {
        let mut focus_specs = BTreeSet::new();
        focus_specs.insert(*target);

        let mut no_specs = instance.no_focus_specs.clone();
        no_specs.append(&mut instance.no_verify_specs.clone());
        no_specs.remove(target);

        Self {
            targets: instance.targets,
            function_specs: instance.function_specs,
            no_verify_specs: no_specs.clone(),
            no_focus_specs: no_specs.clone(),
            focus_specs: focus_specs,
            ignore_aborts: instance.ignore_aborts,
            scenario_specs: instance.scenario_specs,
            datatype_invs: instance.datatype_invs,
            target_modules: instance.target_modules,
            omit_opaque_specs: instance.omit_opaque_specs,
            skip_specs: instance.skip_specs,
        }
    }

    pub fn for_one_module(
        target: &ModuleId,
        instance: FunctionTargetsHolder,
        env: &GlobalEnv,
    ) -> Self {
        let mut focus_specs = BTreeSet::new();
        let mut no_focus_specs = BTreeSet::new();
        no_focus_specs.append(&mut instance.no_focus_specs.clone());

        let mut no_verify_specs: BTreeSet<QualifiedId<FunId>> = BTreeSet::new();
        no_verify_specs.append(&mut instance.no_verify_specs.clone());

        for id in instance.focus_specs() {
            if env.get_function(*id).module_env.get_id() == *target {
                focus_specs.insert(*id);
            } else {
                no_focus_specs.insert(*id);
            }
        }

        for (id, _) in instance.function_specs() {
            if env.get_function(*id).module_env.get_id() != *target {
                no_verify_specs.insert(*id);
            }
        }

        Self {
            focus_specs,
            no_focus_specs,
            no_verify_specs,
            targets: instance.targets,
            function_specs: instance.function_specs,
            ignore_aborts: instance.ignore_aborts,
            scenario_specs: instance.scenario_specs,
            datatype_invs: instance.datatype_invs,
            target_modules: instance.target_modules,
            omit_opaque_specs: instance.omit_opaque_specs,
            skip_specs: instance.skip_specs,
        }
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

    pub fn function_specs(&self) -> &BiBTreeMap<QualifiedId<FunId>, QualifiedId<FunId>> {
        &self.function_specs
    }

    pub fn get_fun_by_spec(&self, id: &QualifiedId<FunId>) -> Option<&QualifiedId<FunId>> {
        self.function_specs.get_by_left(id)
    }

    pub fn get_spec_by_fun(&self, id: &QualifiedId<FunId>) -> Option<&QualifiedId<FunId>> {
        self.function_specs.get_by_right(id)
    }

    pub fn no_verify_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        if self.focus_specs.is_empty() {
            &self.no_verify_specs
        } else {
            &self.no_focus_specs
        }
    }

    pub fn no_focus_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.no_focus_specs
    }

    pub fn focus_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.focus_specs
    }

    pub fn ignore_aborts(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.ignore_aborts
    }

    pub fn scenario_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.scenario_specs
    }

    pub fn target_modules(&self) -> &BTreeSet<ModuleId> {
        &self.target_modules
    }

    pub fn ignores_aborts(&self, id: &QualifiedId<FunId>) -> bool {
        self.ignore_aborts.contains(id)
    }

    pub fn is_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.get_fun_by_spec(id).is_some() || self.scenario_specs.contains(id)
    }

    pub fn is_function_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.get_fun_by_spec(id).is_some()
    }

    pub fn is_verified_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.is_spec(id) && !self.no_verify_specs().contains(id)
    }

    pub fn is_focus_spec(&self, id: &QualifiedId<FunId>) -> bool {
        self.is_spec(id) && !self.no_focus_specs.contains(id)
    }

    pub fn omits_opaque(&self, id: &QualifiedId<FunId>) -> bool {
        self.omit_opaque_specs.contains(id)
    }

    pub fn skip_spec_txt(&self, id: &QualifiedId<FunId>) -> String {
        self.skip_specs.get(id).cloned().unwrap_or_default()
    }

    pub fn skip_specs(&self) -> impl Iterator<Item = &QualifiedId<FunId>> {
        self.skip_specs.keys()
    }

    pub fn specs(&self) -> impl Iterator<Item = &QualifiedId<FunId>> {
        self.function_specs
            .left_values()
            .chain(self.scenario_specs.iter())
    }

    pub fn specs_count(&self, env: &GlobalEnv) -> usize {
        self.function_specs.len() + self.scenario_specs.len() - self.count_system_specs(env)
    }

    pub fn verify_specs_count(&self) -> usize {
        self.function_specs.len() + self.scenario_specs.len() - self.no_verify_specs().len()
    }

    pub fn has_no_verify_spec(&self, id: &QualifiedId<FunId>) -> bool {
        match self.get_spec_by_fun(id) {
            Some(spec_id) => self.no_verify_specs().contains(spec_id),
            None => false,
        }
    }

    pub fn get_inv_by_datatype(&self, id: &QualifiedId<DatatypeId>) -> Option<&QualifiedId<FunId>> {
        self.datatype_invs.get_by_left(id)
    }

    pub fn get_datatype_by_inv(&self, id: &QualifiedId<FunId>) -> Option<&QualifiedId<DatatypeId>> {
        self.datatype_invs.get_by_right(id)
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

        if let Some(KnownAttribute::Verification(VerificationAttribute::Spec { focus, prove, skip, target, no_opaque, ignore_abort })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::Spec)
            .map(|attr| &attr.value)
        {
            if *no_opaque {
                self.omit_opaque_specs.insert(func_env.get_qualified_id());
            }

            if skip.is_some() {
                self.skip_specs.insert(func_env.get_qualified_id(), skip.clone().unwrap());
            }

            if (!*prove && !*focus) || skip.is_some() {
                self.no_verify_specs.insert(func_env.get_qualified_id());
            }

            if *focus {
                self.focus_specs.insert(func_env.get_qualified_id());
            } else {
                self.no_focus_specs.insert(func_env.get_qualified_id());
            }

            if *ignore_abort {
                self.ignore_aborts.insert(func_env.get_qualified_id());
            }

            if target.is_some() {
                let env = func_env.module_env.env;

                match Self::parse_module_access(target.as_ref().unwrap(), env, &func_env.module_env) {
                    Some((module_name, fun_name)) => {
                        let module_env = env.find_module(&module_name).unwrap();
                        Self::process_spec(
                            func_env,
                            &module_env,
                            env,
                            &mut self.function_specs,
                            fun_name,
                        );
                    }
                    None => {
                        let module_name = func_env.module_env.get_full_name_str();

                        env.diag(
                            Severity::Error,
                            &func_env.get_loc(),
                            &format!("Error parsing module path '{}'", module_name),
                        );
                    }
                }
            } else {
                let target_func_env_opt =
                    func_env
                        .get_name_str()
                        .strip_suffix("_spec")
                        .and_then(|name| {
                            func_env
                                .module_env
                                .find_function(func_env.symbol_pool().make(name))
                        });
                match target_func_env_opt {
                    Some(target_func_env) => {
                        self.function_specs.insert(
                            func_env.get_qualified_id(),
                            target_func_env.get_qualified_id(),
                        );
                    }
                    None => {
                        self.scenario_specs.insert(func_env.get_qualified_id());
                    }
                }
            }

            self.target_modules.insert(func_env.module_env.get_id());
        }

        if let Some(KnownAttribute::Verification(VerificationAttribute::SpecOnly { inv_target })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::SpecOnly)
            .map(|attr| &attr.value)
        {
            if func_env.get_name_str().contains("type_inv") {
                return;
            }

            let env = func_env.module_env.env;

            if inv_target.is_some() {
                match Self::parse_module_access(inv_target.as_ref().unwrap(), env, &func_env.module_env) {
                    Some((module_name, struct_name)) => {
                        let module_env = env.find_module(&module_name).unwrap();

                        Self::process_inv(
                            func_env,
                            &module_env,
                            env,
                            &mut self.datatype_invs,
                            struct_name,
                        );
                    }
                    None => {
                        let module_name = func_env.module_env.get_full_name_str();

                        env.diag(
                            Severity::Error,
                            &func_env.get_loc(),
                            &format!("Error parsing module path '{}'", module_name),
                        );
                    }
                }
            } else {
                func_env
                    .get_name_str()
                    .strip_suffix("_inv")
                    .map(|struct_name: &str| {
                        let module_env = &func_env.module_env;
                        Self::process_inv(
                            func_env,
                            module_env,
                            env,
                            &mut self.datatype_invs,
                            struct_name.to_string(),
                        );
                    });
            }
        }
    }

    fn parse_module_access(
        function_spec: &ModuleAccess,
        env: &GlobalEnv,
        current_module: &ModuleEnv,
    ) -> Option<(ModuleName, String)> {
        match &function_spec.value {
            ModuleAccess_::Name(name) => {
                // TODO: Still will not work with other instances, like types or structs (for spec_only edge cases)
                let function_name = name.value.to_string();
                let function_symbol = env.symbol_pool().make(&function_name);
                
                // First try to find the function in the current module
                if current_module.find_function(function_symbol).is_some() {
                    return Some((current_module.get_name().clone(), function_name));
                }

                let handle_index = current_module.data.module.function_handles()
                    .iter()
                    .enumerate()
                    .find_map(|(h_index, handle)| {
                        if function_name == current_module.data.module.identifier_at(handle.name).to_string() {
                            Some(FunctionHandleIndex(h_index.try_into().unwrap()))
                        } else {
                            None
                        }
                    });

                if handle_index.is_some() {
                    let func_env= current_module.get_used_function(handle_index.unwrap());
                    Some((func_env.module_env.get_name().clone(), function_name))
                } else {
                    None
                }
            }
            ModuleAccess_::ModuleAccess(module_ident, name) => {
                let address = module_ident.value.address;
                let module = &module_ident.value.module;

                let addr_bytes = address.into_addr_bytes();
                let module_name = ModuleName::from_address_bytes_and_name(
                    addr_bytes,
                    env.symbol_pool().make(&module.to_string()),
                );

                let function_name = name.value.to_string();
                Some((module_name, function_name))
            }
            ModuleAccess_::Variant(_, _) => {
                // Variant access is not supported in this context
                None
            }
        }
    }

    fn process_spec(
        func_env: &FunctionEnv<'_>,
        module_env: &ModuleEnv<'_>,
        env: &GlobalEnv,
        function_specs: &mut BiBTreeMap<QualifiedId<FunId>, QualifiedId<FunId>>,
        func_name: String,
    ) {
        if let Some(target_func_env) =
            module_env.find_function(func_env.symbol_pool().make(func_name.as_str()))
        {
            let target_id = target_func_env.get_qualified_id();

            if function_specs.contains_right(&target_id) {
                let env = func_env.module_env.env;
                env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!("Duplicate target function: {}", func_name),
                );
            } else {
                function_specs.insert(func_env.get_qualified_id(), target_id);
            }
        } else {
            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                &format!(
                    "Target function '{}' not found in module '{}'",
                    func_name,
                    module_env.get_full_name_str()
                ),
            );
        }
    }

    fn process_inv(
        func_env: &FunctionEnv<'_>,
        module_env: &ModuleEnv<'_>,
        env: &GlobalEnv,
        datatype_invs: &mut BiBTreeMap<QualifiedId<DatatypeId>, QualifiedId<FunId>>,
        struct_name: String,
    ) {
        if let Some(struct_env) =
            module_env.find_struct(env.symbol_pool().make(struct_name.as_str()))
        {
            if datatype_invs.contains_left(&struct_env.get_qualified_id()) {
                env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!(
                        "Duplicate invariant declaration for struct: {}",
                        struct_name
                    ),
                );
            } else {
                datatype_invs.insert(struct_env.get_qualified_id(), func_env.get_qualified_id());
            }
        } else {
            let module_name = func_env.module_env.get_full_name_str();

            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                &format!(
                    "Target struct '{}' not found in module '{}'",
                    struct_name, module_name
                ),
            );
        }
    }

    /// Gets a function target for read-only consumption, for the given variant.
    pub fn get_target<'env>(
        &'env self,
        func_env: &'env FunctionEnv<'env>,
        variant: &FunctionVariant,
    ) -> FunctionTarget<'env> {
        let data = self
            .get_data(&func_env.get_qualified_id(), variant)
            .unwrap_or_else(|| {
                panic!(
                    "expected function target: {} ({:?})",
                    func_env.get_full_name_str(),
                    variant
                )
            });
        FunctionTarget::new(func_env, data)
    }

    pub fn has_target(&self, func_env: &FunctionEnv<'_>, variant: &FunctionVariant) -> bool {
        self.get_data(&func_env.get_qualified_id(), variant)
            .is_some()
    }

    /// Gets all available variants for function.
    pub fn get_target_variants(&self, func_env: &FunctionEnv<'_>) -> Vec<FunctionVariant> {
        self.targets
            .get(&func_env.get_qualified_id())
            .expect("function targets exist")
            .keys()
            .cloned()
            .collect_vec()
    }

    /// Gets targets for all available variants.
    pub fn get_targets<'env>(
        &'env self,
        func_env: &'env FunctionEnv<'env>,
    ) -> Vec<(FunctionVariant, FunctionTarget<'env>)> {
        self.targets
            .get(&func_env.get_qualified_id())
            .expect("function targets exist")
            .iter()
            .map(|(v, d)| (v.clone(), FunctionTarget::new(func_env, d)))
            .collect_vec()
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

    /// Processes the function target data for given function.
    fn process(
        &mut self,
        func_env: &FunctionEnv,
        processor: &dyn FunctionTargetProcessor,
        scc_opt: Option<&[FunctionEnv]>,
    ) {
        let id = func_env.get_qualified_id();
        for variant in self.get_target_variants(func_env) {
            // Remove data so we can own it.
            let data = self.remove_target_data(&id, &variant);
            if let Some(processed_data) =
                processor.process_and_maybe_remove(self, func_env, data, scc_opt)
            {
                // Put back processed data.
                self.insert_target_data(&id, variant, processed_data);
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
        writeln!(f, "Focus specs:")?;
        for spec in self.focus_specs.iter() {
            writeln!(f, "  {}", env.get_function(*spec).get_full_name_str())?;
        }
        writeln!(f, "No verify specs:")?;
        for spec in self.no_verify_specs.iter() {
            writeln!(f, "  {}", env.get_function(*spec).get_full_name_str())?;
        }
        writeln!(f, "No asserts specs:")?;
        for spec in self.ignore_aborts.iter() {
            writeln!(f, "  {}", env.get_function(*spec).get_full_name_str())?;
        }
        writeln!(f, "Scenario specs:")?;
        for spec in self.scenario_specs.iter() {
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
    fn build_call_graph(
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
                let dst_qid = targets
                    .get_callee_spec_qid(&fun_env.get_qualified_id(), &callee)
                    .unwrap_or(&callee);
                let dst_idx = nodes
                    .get(dst_qid)
                    .expect("callee is not in function targets");
                graph.add_edge(*src_idx, *dst_idx, ());
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
        let topological_order = Self::sort_targets_in_topological_order(env, targets);
        hook_before_pipeline(targets);
        for (step_count, processor) in self.processors.iter().enumerate() {
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
