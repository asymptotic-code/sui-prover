use crate::target_filter::TargetFilterOptions;
use bimap::BiBTreeMap;
use codespan_reporting::diagnostic::Severity;
use move_binary_format::file_format::FunctionHandleIndex;
use move_compiler::{
    expansion::ast::{ModuleAccess, ModuleAccess_},
    shared::known_attributes::{
        AttributeKind_, ExternalAttribute, KnownAttribute, VerificationAttribute,
    },
};
use move_model::{
    ast::ModuleName,
    model::{DatatypeId, FunId, FunctionEnv, GlobalEnv, ModuleEnv, ModuleId, QualifiedId},
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModuleExternalSpecAttribute {
    Function(QualifiedId<FunId>),
    Module(ModuleId),
}

#[derive(Debug, Clone)]
pub struct PackageTargets {
    target_specs: BTreeSet<QualifiedId<FunId>>,
    no_verify_specs: BTreeSet<QualifiedId<FunId>>,
    abort_check_functions: BTreeSet<QualifiedId<FunId>>,
    pure_functions: BTreeSet<QualifiedId<FunId>>,
    skipped_specs: BTreeMap<QualifiedId<FunId>, String>,
    ignore_aborts: BTreeSet<QualifiedId<FunId>>,
    omit_opaque_specs: BTreeSet<QualifiedId<FunId>>,
    focus_specs: BTreeSet<QualifiedId<FunId>>,
    scenario_specs: BTreeSet<QualifiedId<FunId>>,
    spec_boogie_options: BTreeMap<QualifiedId<FunId>, String>,
    spec_timeouts: BTreeMap<QualifiedId<FunId>, u64>,
    loop_invariants: BTreeMap<QualifiedId<FunId>, BiBTreeMap<QualifiedId<FunId>, usize>>,
    module_external_attributes: BTreeMap<ModuleId, BTreeSet<ModuleExternalSpecAttribute>>,
    all_specs: BTreeMap<QualifiedId<FunId>, BTreeSet<QualifiedId<FunId>>>,
    all_datatypes_invs: BTreeMap<QualifiedId<DatatypeId>, BTreeSet<QualifiedId<FunId>>>,
    system_specs: BTreeSet<QualifiedId<FunId>>,
    allow_focus_attr: bool,
}

impl PackageTargets {
    pub fn new(env: &GlobalEnv, filter: TargetFilterOptions, allow_focus_attr: bool) -> Self {
        let mut s = Self {
            target_specs: BTreeSet::new(),
            abort_check_functions: BTreeSet::new(),
            pure_functions: BTreeSet::new(),
            skipped_specs: BTreeMap::new(),
            no_verify_specs: BTreeSet::new(),
            ignore_aborts: BTreeSet::new(),
            omit_opaque_specs: BTreeSet::new(),
            focus_specs: BTreeSet::new(),
            scenario_specs: BTreeSet::new(),
            spec_boogie_options: BTreeMap::new(),
            spec_timeouts: BTreeMap::new(),
            loop_invariants: BTreeMap::new(),
            module_external_attributes: BTreeMap::new(),
            all_specs: BTreeMap::new(),
            all_datatypes_invs: BTreeMap::new(),
            system_specs: BTreeSet::new(),
            allow_focus_attr,
        };
        s.collect_targets(env, filter);
        s
    }

    fn process_spec(&mut self, spec_func_env: &FunctionEnv<'_>, target_func_env: &FunctionEnv<'_>) {
        if self
            .all_specs
            .get(&target_func_env.get_qualified_id())
            .is_none()
        {
            self.all_specs
                .insert(target_func_env.get_qualified_id(), BTreeSet::new());
        }

        if !self
            .all_specs
            .get_mut(&target_func_env.get_qualified_id())
            .unwrap()
            .insert(spec_func_env.get_qualified_id())
        {
            let env = spec_func_env.module_env.env;
            env.diag(
                Severity::Error,
                &target_func_env.get_loc(),
                &format!(
                    "Duplicate spec function: {}",
                    target_func_env.get_name_str()
                ),
            );
        }
    }

    fn parse_module_access(
        ms: &ModuleAccess,
        current_module: &ModuleEnv,
    ) -> Option<(ModuleName, String)> {
        match &ms.value {
            ModuleAccess_::Name(name) => {
                // TODO: Still will not work with other instances, like types or structs (for spec_only edge cases)
                let function_name = name.value.to_string();
                let function_symbol = current_module.env.symbol_pool().make(&function_name);

                // First try to find the function in the current module
                if current_module.find_function(function_symbol).is_some() {
                    return Some((current_module.get_name().clone(), function_name));
                }

                let handle_index = current_module
                    .data
                    .module
                    .function_handles()
                    .iter()
                    .enumerate()
                    .find_map(|(h_index, handle)| {
                        if function_name
                            == current_module
                                .data
                                .module
                                .identifier_at(handle.name)
                                .to_string()
                        {
                            Some(FunctionHandleIndex(h_index.try_into().unwrap()))
                        } else {
                            None
                        }
                    });

                if handle_index.is_some() {
                    let func_env = current_module.get_used_function(handle_index.unwrap());
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
                    current_module.env.symbol_pool().make(&module.to_string()),
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

    fn process_loop_inv(
        &mut self,
        func_env: &FunctionEnv<'_>,
        module_env: &ModuleEnv<'_>,
        fun_name: String,
        label: usize,
    ) {
        let env = module_env.env;

        if let Some(target_func_env) =
            module_env.find_function(func_env.symbol_pool().make(fun_name.as_str()))
        {
            if let Some(existing) = self
                .loop_invariants
                .get_mut(&target_func_env.get_qualified_id())
            {
                match existing.insert(func_env.get_qualified_id(), label) {
                    bimap::Overwritten::Neither => {}
                    bimap::Overwritten::Left(..) => {
                        env.diag(
                            Severity::Error,
                            &func_env.get_loc(),
                            &format!(
                                "Duplicated Loop Invariant Function {} in {}",
                                func_env.get_full_name_str(),
                                fun_name
                            ),
                        );
                        return;
                    }
                    bimap::Overwritten::Right(..) => {
                        env.diag(
                            Severity::Error,
                            &func_env.get_loc(),
                            &format!("Duplicated Loop Invariant Label {} in {}", label, fun_name),
                        );
                        return;
                    }
                    bimap::Overwritten::Both(..) | bimap::Overwritten::Pair(..) => {
                        env.diag(
                            Severity::Error,
                            &func_env.get_loc(),
                            &format!(
                                "Duplicated Loop Invariant Function {} and Label {} in {}",
                                func_env.get_full_name_str(),
                                label,
                                fun_name
                            ),
                        );
                    }
                }
            } else {
                self.loop_invariants
                    .insert(target_func_env.get_qualified_id(), {
                        let mut map = BiBTreeMap::new();
                        map.insert(func_env.get_qualified_id(), label);
                        map
                    });
            }
        } else {
            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                &format!("Invalid Loop Invariant Function Provided: {}", fun_name),
            );
        }
    }

    fn process_inv(&mut self, func_env: &FunctionEnv, module_env: &ModuleEnv, struct_name: String) {
        let env = module_env.env;
        if let Some(struct_env) =
            module_env.find_struct(env.symbol_pool().make(struct_name.as_str()))
        {
            if self
                .all_datatypes_invs
                .get(&struct_env.get_qualified_id())
                .is_none()
            {
                self.all_datatypes_invs
                    .insert(struct_env.get_qualified_id(), BTreeSet::new());
            }

            if !self
                .all_datatypes_invs
                .get_mut(&struct_env.get_qualified_id())
                .unwrap()
                .insert(func_env.get_qualified_id())
            {
                env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!(
                        "Duplicate invariant declaration for struct: {}",
                        struct_name
                    ),
                );
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

    fn collect_targets(&mut self, env: &GlobalEnv, filter: TargetFilterOptions) {
        for module_env in env.get_modules() {
            for func_env in module_env.get_functions() {
                self.check_spec_scope(&func_env, filter.clone());
                self.check_spec_only_scope(&func_env, filter.clone());
                self.check_abort_check_scope(&func_env, filter.clone());
            }
            self.handle_module_explicit_spec_attributes(&module_env);
        }

        if !self.focus_specs.is_empty() {
            for spec in &self.target_specs {
                if !self.focus_specs.contains(spec) {
                    self.no_verify_specs.insert(*spec);
                }
            }
            self.target_specs = self.focus_specs.clone();
        }
    }

    fn check_spec_only_scope(&mut self, func_env: &FunctionEnv, filter: TargetFilterOptions) {
        if let Some(KnownAttribute::Verification(VerificationAttribute::SpecOnly {
            inv_target,
            loop_inv,
            explicit_spec_modules: _,
            explicit_specs: _,
        })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::SpecOnly)
            .map(|attr| &attr.value)
        {
            if func_env.get_name_str().contains("type_inv") {
                return;
            }

            let env = func_env.module_env.env;

            if let Some(loop_inv) = loop_inv {
                match Self::parse_module_access(&loop_inv.target, &func_env.module_env) {
                    Some((module_name, fun_name)) => {
                        let module_env = env.find_module(&module_name).unwrap();
                        self.process_loop_inv(func_env, &module_env, fun_name, loop_inv.label);
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
                return;
            }

            if inv_target.is_some() {
                match Self::parse_module_access(inv_target.as_ref().unwrap(), &func_env.module_env)
                {
                    Some((module_name, struct_name)) => {
                        let module_env = env.find_module(&module_name).unwrap();

                        self.process_inv(func_env, &module_env, struct_name);
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
                        self.process_inv(func_env, &func_env.module_env, struct_name.to_string());
                    });
            }
        }
    }

    fn check_spec_scope(&mut self, func_env: &FunctionEnv, filter: TargetFilterOptions) {
        let env = func_env.module_env.env;
        if let Some(KnownAttribute::Verification(VerificationAttribute::Spec {
            focus,
            prove,
            skip,
            target,
            no_opaque,
            ignore_abort,
            boogie_opt,
            timeout,
        })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::Spec)
            .map(|attr| &attr.value)
        {
            if Self::system_spec(&func_env.get_qualified_id(), env) {
                self.system_specs.insert(func_env.get_qualified_id());
            }

            if let Some(opt) = boogie_opt {
                self.spec_boogie_options
                    .insert(func_env.get_qualified_id(), opt.clone());
            }

            if let Some(timeout) = timeout {
                self.spec_timeouts
                    .insert(func_env.get_qualified_id(), *timeout);
            }

            if *no_opaque {
                self.omit_opaque_specs.insert(func_env.get_qualified_id());
            }

            if *ignore_abort {
                self.ignore_aborts.insert(func_env.get_qualified_id());
            }

            if !func_env.module_env.is_target()
                || skip.is_some()
                || !filter.is_targeted(func_env)
                || (!*prove && !*focus)
            {
                self.no_verify_specs.insert(func_env.get_qualified_id());
            } else {
                if *focus {
                    if !self.allow_focus_attr {
                        env.diag(
                            Severity::Error,
                            &func_env.get_loc(),
                            "The 'focus' attribute is restricted in CI mode.",
                        );
                        return;
                    }
                    self.focus_specs.insert(func_env.get_qualified_id());
                }
                self.target_specs.insert(func_env.get_qualified_id());
            }

            if target.is_some() {
                match Self::parse_module_access(target.as_ref().unwrap(), &func_env.module_env) {
                    Some((module_name, func_name)) => {
                        let module_env = env.find_module(&module_name).unwrap();
                        if let Some(target_func_env) = module_env
                            .find_function(func_env.symbol_pool().make(func_name.as_str()))
                        {
                            self.process_spec(func_env, &target_func_env);
                        } else {
                            env.diag(
                                Severity::Error,
                                &func_env.get_loc(),
                                &format!(
                                    "Target function '{}' not found in module '{}'",
                                    func_name,
                                    module_env.get_full_name_str(),
                                ),
                            );
                        }
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
                        self.process_spec(func_env, &target_func_env);
                    }
                    None => {
                        // scenario specs either ignore aborts or do not have any asserts
                        if !*ignore_abort
                            && func_env
                                .get_called_functions()
                                .iter()
                                .any(|f| *f == func_env.module_env.env.asserts_qid())
                        {
                            func_env.module_env.env.diag(
                                Severity::Error,
                                &func_env.get_loc(),
                                "Scenario specs either ignore aborts or do not have any asserts.",
                            );
                            return;
                        }
                        self.scenario_specs.insert(func_env.get_qualified_id());
                    }
                }
            }
        }
    }

    fn check_abort_check_scope(&mut self, func_env: &FunctionEnv, filter: TargetFilterOptions) {
        if let Some(KnownAttribute::External(ExternalAttribute { attrs })) = func_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::External)
            .map(|attr| &attr.value)
        {
            if attrs
                .into_iter()
                .any(|attr| attr.2.value.name().value.as_str() == "no_abort".to_string())
            {
                self.abort_check_functions
                    .insert(func_env.get_qualified_id());
            }
            if attrs
                .into_iter()
                .any(|attr| attr.2.value.name().value.as_str() == "pure".to_string())
            {
                self.pure_functions.insert(func_env.get_qualified_id());
            }
        }
    }

    pub fn is_spec(&self, func_id: &QualifiedId<FunId>) -> bool {
        self.target_specs.contains(func_id) || self.no_verify_specs.contains(func_id)
    }

    pub fn get_specs(&self, func_id: &QualifiedId<FunId>) -> Option<BTreeSet<QualifiedId<FunId>>> {
        self.all_specs.get(func_id).cloned()
    }

    pub fn find_target_spec(&self, spec_id: &QualifiedId<FunId>) -> Option<QualifiedId<FunId>> {
        for (target_id, specs) in &self.all_specs {
            if specs.contains(spec_id) {
                return Some(*target_id);
            }
        }
        None
    }

    pub fn find_datatype_inv(
        &self,
        fun_id: &QualifiedId<FunId>,
    ) -> Option<QualifiedId<DatatypeId>> {
        for (struct_id, funs) in &self.all_datatypes_invs {
            if funs.contains(fun_id) {
                return Some(*struct_id);
            }
        }
        None
    }

    fn system_spec(qid: &QualifiedId<FunId>, env: &GlobalEnv) -> bool {
        let func_env = env.get_function(*qid);
        let module_env = &func_env.module_env;
        if module_env.get_name().addr() == &0u16.into() {
            let module_name = module_env
                .get_name()
                .name()
                .display(env.symbol_pool())
                .to_string();
            if GlobalEnv::SPECS_MODULES_NAMES.contains(&module_name.as_str()) {
                return true;
            }
        }
        false
    }

    pub fn is_system_spec(&self, qid: &QualifiedId<FunId>) -> bool {
        self.system_specs.contains(qid)
    }

    fn handle_module_explicit_spec_attributes(&mut self, module_env: &ModuleEnv) {
        let mut result: BTreeSet<ModuleExternalSpecAttribute> = BTreeSet::new();

        if let Some(KnownAttribute::Verification(VerificationAttribute::SpecOnly {
            inv_target: _,
            loop_inv: _,
            explicit_spec_modules,
            explicit_specs,
        })) = module_env
            .get_toplevel_attributes()
            .get_(&AttributeKind_::SpecOnly)
            .map(|attr| &attr.value)
        {
            for mi in explicit_spec_modules {
                let name = ModuleName::from_address_bytes_and_name(
                    mi.value.address.into_addr_bytes(),
                    module_env
                        .env
                        .symbol_pool()
                        .make(&mi.value.module.to_string()),
                );
                if let Some(module) = module_env.env.find_module(&name) {
                    result.insert(ModuleExternalSpecAttribute::Module(module.get_id()));
                } else {
                    module_env.env.diag(
                        Severity::Error,
                        &module_env.get_loc(),
                        &format!(
                            "Error parsing module path in explicit_spec_module '{}'",
                            module_env.get_full_name_str()
                        ),
                    );
                    return;
                }
            }

            for ms in explicit_specs {
                match Self::parse_module_access(ms, module_env) {
                    Some((module_name, fun_name)) => {
                        let target_module_env = module_env.env.find_module(&module_name).unwrap();
                        if let Some(func_env) = target_module_env
                            .find_function(module_env.env.symbol_pool().make(&fun_name))
                        {
                            result.insert(ModuleExternalSpecAttribute::Function(
                                func_env.get_qualified_id(),
                            ));
                        } else {
                            module_env.env.diag(
                                Severity::Error,
                                &module_env.get_loc(),
                                &format!(
                                    "Function '{}' not found in module '{}'",
                                    fun_name,
                                    target_module_env.get_full_name_str(),
                                ),
                            );
                            return;
                        }
                    }
                    None => {
                        module_env.env.diag(
                            Severity::Error,
                            &module_env.get_loc(),
                            &format!(
                                "Error parsing module path in explicit_spec_module '{}'",
                                module_env.get_full_name_str()
                            ),
                        );
                        return;
                    }
                }
            }
        }

        self.module_external_attributes
            .insert(module_env.get_id(), result.clone());
    }

    pub fn is_belongs_to_module_explicit_specs(
        &mut self,
        module_env: &ModuleEnv,
        qid: QualifiedId<FunId>,
    ) -> bool {
        if let Some(external_attrs) = self.module_external_attributes.get(&module_env.get_id()) {
            external_attrs.contains(&ModuleExternalSpecAttribute::Module(qid.module_id))
                || external_attrs.contains(&ModuleExternalSpecAttribute::Function(qid))
        } else {
            false
        }
    }

    pub fn has_specs(&self) -> bool {
        (self.target_specs.len() + self.no_verify_specs.len() - self.system_specs.len()) > 0
    }

    pub fn has_function_checks(&self) -> bool {
        !self.abort_check_functions.is_empty() || !self.pure_functions.is_empty()
    }

    pub fn has_focus_specs(&self) -> bool {
        !self.focus_specs.is_empty()
    }

    pub fn ignores_aborts(&self, func_id: &QualifiedId<FunId>) -> bool {
        self.ignore_aborts.contains(func_id)
    }

    pub fn is_verified_spec(&self, func_id: &QualifiedId<FunId>) -> bool {
        self.target_specs.contains(func_id)
    }

    pub fn has_spec_boogie_options(&self) -> bool {
        !self.spec_boogie_options.is_empty()
    }

    pub fn target_modules(&self) -> BTreeSet<ModuleId> {
        self.target_specs.iter().map(|qid| qid.module_id).collect()
    }

    pub fn spec_abort_check_verify_modules(&self) -> BTreeSet<ModuleId> {
        self.no_verify_specs
            .iter()
            .filter(|qid| !self.is_system_spec(*qid))
            .map(|qid| qid.module_id)
            .collect()
    }

    pub fn target_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.target_specs
    }

    pub fn no_verify_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.no_verify_specs
    }

    pub fn abort_check_functions(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.abort_check_functions
    }

    pub fn pure_functions(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.pure_functions
    }

    pub fn skipped_specs(&self) -> &BTreeMap<QualifiedId<FunId>, String> {
        &self.skipped_specs
    }

    pub fn ignore_aborts(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.ignore_aborts
    }

    pub fn omit_opaque_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.omit_opaque_specs
    }

    pub fn scenario_specs(&self) -> &BTreeSet<QualifiedId<FunId>> {
        &self.scenario_specs
    }

    pub fn spec_boogie_options(&self) -> &BTreeMap<QualifiedId<FunId>, String> {
        &self.spec_boogie_options
    }

    pub fn spec_timeouts(&self) -> &BTreeMap<QualifiedId<FunId>, u64> {
        &self.spec_timeouts
    }

    pub fn loop_invariants(
        &self,
    ) -> &BTreeMap<QualifiedId<FunId>, BiBTreeMap<QualifiedId<FunId>, usize>> {
        &self.loop_invariants
    }
}
