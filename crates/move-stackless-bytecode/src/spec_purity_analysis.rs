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
                | MoveBytecode::VecSwap(_) => {
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
        env: &GlobalEnv,
    ) -> BTreeSet<Loc> {
        let mut impure_locs = BTreeSet::new();

        // Only run the bytecode purity analysis for spec functions
        if targets.is_function_spec(&func_env.get_qualified_id()) {
            // Get the actual bytecode from the function
            let bytecode = func_env.get_bytecode();

            // Create a function target to access bytecode locations
            if let Some(target_data) =
                targets.get_data(&func_env.get_qualified_id(), &FunctionVariant::Baseline)
            {
                let target = FunctionTarget::new(func_env, target_data);
                impure_locs = self.bytecode_purity(bytecode, &target);

                // Report errors for impure bytecode in spec functions
                if !impure_locs.is_empty() {
                    println!(
                        "  Found {} mutable bytecode instructions",
                        impure_locs.len()
                    );
                    for loc in impure_locs.iter() {
                        env.diag(
                            Severity::Error,
                            loc,
                            "Spec function contains mutable bytecode instructions",
                        );
                    }
                }
            }
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
                            let function_name = module.get_function(*func_id).get_full_name_str();

                            println!("Analyzing call to {}::{}", module_name, function_name);

                            if SKIP_MODULES.contains(&module_name.as_str()) {
                                continue;
                            }

                            // Process network calls
                            if NETWORK_MODULES.contains(&module_name.as_str()) {
                                println!(
                                    "    Marking as impure due to network module: {}",
                                    module_name
                                );
                                network_results.insert(target.get_bytecode_loc(*attr));
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

                            // Propagate network call impurity
                            if annotation.is_network_call {
                                println!("    Marking as impure because called function is calling a network module: {}::{}", module_name, function_name);
                                network_results.insert(target.get_bytecode_loc(*attr));
                            }

                            // Process mutable reference impurity
                            if annotation.is_mutable_reference {
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

        println!(
            "Starting analysis for function: {}",
            func_env.get_full_name_str()
        );

        let mutable_references = self.find_mutable_reference(&func_env, targets);

        let underlying_func_id = targets.get_fun_by_spec(&func_env.get_qualified_id());
        let code = func_target.get_bytecode();
        let call_operation = if underlying_func_id.is_some() {
            self.find_operation_in_function(*underlying_func_id.unwrap(), code)
        } else {
            None
        };

        // Use process_calls instead of find_network_calls
        let (network_calls, mut_ref_calls) =
            self.process_calls(code, targets, &func_target, &env, &call_operation);

        // Check bytecode purity for spec functions
        let bytecode_impurities = self.check_bytecode_purity_for_spec(func_env, targets, &env);

        let is_spec = targets.is_function_spec(&func_env.get_qualified_id());
        if is_spec {
            println!("Inserting errors");
            if !network_calls.is_empty() {
                println!("  Found {} network calls", network_calls.len());
                for loc in network_calls.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function is calling a network module",
                    );
                }
            }
            if !mut_ref_calls.is_empty() {
                println!(
                    "  Found {} calls with mutable references",
                    mut_ref_calls.len()
                );
                for loc in mut_ref_calls.iter() {
                    env.diag(
                        Severity::Error,
                        loc,
                        "Spec function is calling a function that uses mutable references",
                    );
                }
            }
        }

        PurityVerificationInfo {
            is_network_call: !network_calls.is_empty(),
            is_mutable_reference: !mutable_references.is_empty() || !bytecode_impurities.is_empty(),
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
