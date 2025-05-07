use std::collections::BTreeSet;

use codespan_reporting::diagnostic::Severity;
use move_binary_format::file_format::Bytecode as MoveBytecode;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, Loc, QualifiedId};

use crate::{
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{Bytecode, Operation},
};

pub const NETWORK_MODULES: [&str; 1] = ["transfer"];
// pub const NETWORK_MODULES: [&str; 2] = ["transfer", "event"];
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
                    println!("  Found mutable reference parameter");
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

    fn bytecode_purity(&self, bytecode: &[MoveBytecode]) -> bool {
        for bc in bytecode {
            match bc {
                MoveBytecode::MutBorrowLoc(_)
                | MoveBytecode::MutBorrowField(_)
                | MoveBytecode::MutBorrowFieldGeneric(_)
                | MoveBytecode::VecMutBorrow(_)
                | MoveBytecode::WriteRef
                | MoveBytecode::VecPushBack(_)
                | MoveBytecode::VecPopBack(_)
                | MoveBytecode::VecSwap(_) => {
                    return false;
                }
                _ => {}
            }
        }

        true
    }

    pub fn find_network_calls(
        &self,
        code: &[Bytecode],
        targets: &FunctionTargetsHolder,
        target: &FunctionTarget,
        env: &GlobalEnv,
        skip: &Option<Operation>,
    ) -> BTreeSet<Loc> {
        let mut results = BTreeSet::new();

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
                            let function_name = module.get_function(*func_id).get_full_name_str();

                            println!("Looking for network calls");
                            println!("  Found call to {}::{}", module_name, function_name);

                            if SKIP_MODULES.contains(&module_name.as_str()) {
                                continue;
                            }

                            if NETWORK_MODULES.contains(&module_name.as_str()) {
                                println!(
                                    "    Marking as impure due to network module: {}",
                                    module_name
                                );
                                results.insert(target.get_bytecode_loc(*attr));
                            }

                            let internal_data = targets
                                .get_data(&mod_id.qualified(*func_id), &FunctionVariant::Baseline);
                            if internal_data.is_none() {
                                println!(
                                    "    No function data found for {}::{}",
                                    module_name, function_name
                                );
                                continue;
                            }

                            let annotation = internal_data
                                .unwrap()
                                .annotations
                                .get::<PurityVerificationInfo>()
                                .expect("Function expect to be already scanned");

                            if annotation.is_network_call {
                                println!("    Marking as impure because called function is calling a network module: {}::{}", module_name, function_name);
                                results.insert(target.get_bytecode_loc(*attr));
                            }

                            if annotation.is_mutable_reference {
                                let func = module.get_function(func_id.clone());
                                let func_bytecode: &[move_binary_format::file_format::Bytecode] = func.get_bytecode();

                                if !self.bytecode_purity(func_bytecode) {
                                    println!("    Marking as impure because called function is calling a mutable reference: {}::{}", module_name, function_name);
                                    results.insert(target.get_bytecode_loc(*attr));
                                }
                            }
                        }
                        _ => {}
                    };
                }
                _ => {}
            }
        }

        results
    }

    fn analyse(
        &self,
        func_env: &FunctionEnv,
        targets: &FunctionTargetsHolder,
        data: &FunctionData,
    ) -> PurityVerificationInfo {
        let is_spec = targets.is_function_spec(&func_env.get_qualified_id());
        let env = func_env.module_env.env;
        let func_target = FunctionTarget::new(func_env, data);

        println!(
            "Starting analysis for function: {}",
            func_env.get_full_name_str()
        );

        let underlying_func_id = targets.get_fun_by_spec(&func_env.get_qualified_id());
        if underlying_func_id.is_some() {
            println!("  This is a spec function with underlying implementation");
        }

        let code = func_target.get_bytecode();

        let mutable_references = self.find_mutable_reference(&func_env, targets);
        if mutable_references.len() > 0 {
            println!("  Found {} mutable references", mutable_references.len());
        }

        let call_operation = if underlying_func_id.is_some() {
            self.find_operation_in_function(*underlying_func_id.unwrap(), code)
        } else {
            None
        };
        println!("  Call operation: {:?}", call_operation);

        let network_calls =
            self.find_network_calls(code, targets, &func_target, &env, &call_operation);
        if network_calls.len() > 0 {
            println!("  Found {} network calls", network_calls.len());
        }
        println!("  Network calls: {:?}", network_calls);

        if is_spec {
            println!("Inserting errors");
            if network_calls.len() > 0 {
                println!("Inserting network call errors");
                for loc in network_calls.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function is calling a network module",
                    );
                }
            }
            if mutable_references.len() > 0 {
                println!("Inserting mutable reference errors");
                for loc in mutable_references.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function is calling a mutable reference",
                    );
                }
            }
        }

        PurityVerificationInfo {
            is_network_call: network_calls.len() > 0,
            is_mutable_reference: mutable_references.len() > 0,
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
        println!("Processing function: {}", func_env.get_full_name_str());

        let annotation = data.annotations.get::<PurityVerificationInfo>();

        println!(
            "  Existing annotation: {}",
            if annotation.is_some() {
                "found"
            } else {
                "not found"
            }
        );

        let annotation_data = if annotation.is_some() {
            println!(
                "  Using existing annotations with is_network_call = {} and is_mutable_reference = {}",
                annotation.unwrap().is_network_call,
                annotation.unwrap().is_mutable_reference
            );
            annotation.unwrap().clone()
        } else {
            println!("  Calculating new annotations");
            self.analyse(func_env, targets, &data)
        };

        println!(
            "  Annotation result for {}: network_call = {}, mutable_ref = {}",
            func_env.get_full_name_str(),
            annotation_data.is_network_call,
            annotation_data.is_mutable_reference
        );

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

        println!("  Fixedpoint: {}", fixedpoint);

        data.annotations
            .set::<PurityVerificationInfo>(annotation_data, fixedpoint);

        println!(
            "  Stored annotation for function: {} \n",
            func_env.get_full_name_str()
        );

        data
    }

    fn name(&self) -> String {
        "spec_purity_analysis".to_string()
    }
}
