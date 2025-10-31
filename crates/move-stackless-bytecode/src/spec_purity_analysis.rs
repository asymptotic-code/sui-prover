use std::collections::BTreeSet;

use codespan_reporting::diagnostic::Severity;
use move_binary_format::file_format::Bytecode as MoveBytecode;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, Loc, QualifiedId};

use crate::{
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{AttrId, Bytecode, Operation},
};

pub const NETWORK_MODULES: [&str; 2] = ["transfer", "event"];
pub const SKIP_MODULES: [&str; 2] = [GlobalEnv::PROVER_MODULE_NAME, GlobalEnv::SPEC_MODULE_NAME];

#[derive(Clone, Debug)]
pub struct PurityVerificationInfo {
    pub is_network_call: bool,
    pub is_mutable_reference: bool,
}

impl Default for PurityVerificationInfo {
    fn default() -> Self {
        Self {
            is_network_call: false,
            is_mutable_reference: false,
        }
    }
}

pub struct SpecPurityAnalysis();

impl SpecPurityAnalysis {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    pub fn find_mutable_reference(
        &self,
        func_env: &FunctionEnv,
        targets: &FunctionTargetsHolder,
    ) -> BTreeSet<Loc> {
        let mut results = BTreeSet::new();
        if !targets.is_spec(&func_env.get_qualified_id()) {
            for param in func_env.get_parameters() {
                if param.1.is_mutable_reference() {
                    results.insert(func_env.get_loc());
                }
            }
        }

        results
    }

    pub fn find_operation_in_function(
        &self,
        target_id: QualifiedId<FunId>,
        code: &[Bytecode],
    ) -> Option<Operation> {
        for cp in code {
            match cp {
                Bytecode::Call(_, _, operation, _, _) => {
                    match operation {
                        Operation::Function(mod_id, fun_id, _) => {
                            let callee_id = mod_id.qualified(*fun_id);
                            if callee_id == target_id {
                                return Some(operation.clone());
                            }
                        }
                        _ => {}
                    };
                }
                _ => {}
            }
        }

        None
    }

    fn bytecode_purity(&self, bytecode: &[MoveBytecode], target: &FunctionTarget) -> BTreeSet<Loc> {
        let mut impure_locs = BTreeSet::new();
        for (offset, bc) in bytecode.iter().enumerate() {
            match bc {
                MoveBytecode::MutBorrowLoc(_)
                | MoveBytecode::MutBorrowField(_)
                | MoveBytecode::MutBorrowFieldGeneric(_)
                | MoveBytecode::VecMutBorrow(_)
                | MoveBytecode::WriteRef
                | MoveBytecode::VecPushBack(_)
                | MoveBytecode::VecPopBack(_)
                | MoveBytecode::VecSwap(_)
                | MoveBytecode::UnpackVariantMutRef(_)
                | MoveBytecode::UnpackVariantGenericMutRef(_) => {
                    impure_locs.insert(target.get_bytecode_loc(AttrId::new(offset)));
                }
                _ => {}
            }
        }

        impure_locs
    }

    fn check_bytecode_purity_for_spec(
        &self,
        func_env: &FunctionEnv,
        targets: &FunctionTargetsHolder,
    ) -> BTreeSet<Loc> {
        let mut impure_locs = BTreeSet::new();

        let bytecode = func_env.get_bytecode();

        if let Some(target_data) =
            targets.get_data(&func_env.get_qualified_id(), &FunctionVariant::Baseline)
        {
            let target = FunctionTarget::new(func_env, target_data);
            impure_locs = self.bytecode_purity(bytecode, &target);
        }

        impure_locs
    }

    pub fn process_calls(
        &self,
        code: &[Bytecode],
        targets: &FunctionTargetsHolder,
        target: &FunctionTarget,
        env: &GlobalEnv,
        skip: &Option<Operation>,
    ) -> (BTreeSet<Loc>, BTreeSet<Loc>) {
        let mut network_results = BTreeSet::new();
        let mut mutable_ref_results = BTreeSet::new();

        for cp in code {
            match cp {
                Bytecode::Call(attr, _, operation, _, _) => {
                    if skip.is_some() && skip.clone().unwrap() == *operation {
                        continue;
                    }
                    match operation {
                        Operation::Function(mod_id, func_id, _) => {
                            let module = env.get_module(*mod_id);
                            let module_name = env.symbol_pool().string(module.get_name().name());

                            if SKIP_MODULES.contains(&module_name.as_str()) {
                                continue;
                            }

                            // Process network calls
                            if NETWORK_MODULES.contains(&module_name.as_str()) {
                                network_results.insert(target.get_bytecode_loc(*attr));
                            }

                            let internal_data = targets
                                .get_data(&mod_id.qualified(*func_id), &FunctionVariant::Baseline);
                            if internal_data.is_none() {
                                continue;
                            }

                            let annotation = internal_data
                                .unwrap()
                                .annotations
                                .get::<PurityVerificationInfo>();

                            let annotation_info = annotation.cloned().unwrap_or_default();

                            // Propagate network call impurity
                            if annotation_info.is_network_call {
                                network_results.insert(target.get_bytecode_loc(*attr));
                            }

                            // Process mutable reference impurity
                            if annotation_info.is_mutable_reference {
                                mutable_ref_results.insert(target.get_bytecode_loc(*attr));
                            }
                        }
                        _ => {}
                    };
                }
                _ => {}
            }
        }

        (network_results, mutable_ref_results)
    }

    fn analyse(
        &self,
        func_env: &FunctionEnv,
        targets: &FunctionTargetsHolder,
        data: &FunctionData,
    ) -> PurityVerificationInfo {
        let env = func_env.module_env.env;
        let func_target = FunctionTarget::new(func_env, data);

        let mutable_references = self.find_mutable_reference(&func_env, targets);

        let underlying_func_id = targets.get_fun_by_spec(&func_env.get_qualified_id());
        let code = func_target.get_bytecode();
        let call_operation = if underlying_func_id.is_some() {
            self.find_operation_in_function(*underlying_func_id.unwrap(), code)
        } else {
            None
        };

        let (network_calls, mut_ref_calls) =
            self.process_calls(code, targets, &func_target, &env, &call_operation);

        let is_spec = targets.is_function_spec(&func_env.get_qualified_id());
        if is_spec {
            if underlying_func_id.is_some() && call_operation.is_none() {
                let spec_name = func_env.get_full_name_str();
                let target_func_env = env.get_function(*underlying_func_id.unwrap());
                let target_name = target_func_env.get_full_name_str();

                env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!(
                        "Spec function `{}` should call target function `{}`",
                        spec_name, target_name
                    ),
                );
            }

            if !network_calls.is_empty() {
                for loc in network_calls.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function is calling a network module",
                    );
                }
            }
            if !mut_ref_calls.is_empty() {
                for loc in mut_ref_calls.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function is calling a function that uses mutable references",
                    );
                }
            }
            let bytecode_impurities = self.check_bytecode_purity_for_spec(func_env, targets);
            if !bytecode_impurities.is_empty() {
                for loc in bytecode_impurities.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function contains mutable bytecode instructions",
                    );
                }
            }
        }

        PurityVerificationInfo {
            is_network_call: !network_calls.is_empty(),
            is_mutable_reference: !mutable_references.is_empty(),
        }
    }
}

impl FunctionTargetProcessor for SpecPurityAnalysis {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        mut data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let annotation = data.annotations.get::<PurityVerificationInfo>();

        let annotation_data = if annotation.is_some() {
            annotation.unwrap().clone()
        } else {
            self.analyse(func_env, targets, &data)
        };

        let fixedpoint = match scc_opt {
            None => true,
            Some(_) => match data.annotations.get::<PurityVerificationInfo>() {
                None => false,
                Some(old_annotation) => {
                    old_annotation.is_network_call == annotation_data.is_network_call
                        && old_annotation.is_mutable_reference
                            == annotation_data.is_mutable_reference
                }
            },
        };

        data.annotations
            .set::<PurityVerificationInfo>(annotation_data, fixedpoint);

        data
    }

    fn name(&self) -> String {
        "spec_purity_analysis".to_string()
    }
}
