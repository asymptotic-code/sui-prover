use std::collections::{BTreeMap, BTreeSet, HashSet};
use codespan_reporting::diagnostic::Severity;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, Loc, QualifiedId};
use move_binary_format::file_format::Bytecode as MoveBytecode;
use std::cell::RefCell;

use crate::{function_target::{FunctionData, FunctionTarget}, function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant}, stackless_bytecode::{Bytecode, Operation}, stackless_bytecode_generator::StacklessBytecodeGenerator};

pub const RESTRICTED_MODULES: [&str; 3] = ["transfer", "event", "emit"];

#[derive(Clone)]
pub struct PurityVerificationInfo {
    pub is_pure: bool,
}

impl Default for PurityVerificationInfo {
    fn default() -> Self {
        Self { is_pure: true }
    }
}

pub struct SpecPurityAnalysis {
    function_purity_cache: RefCell<BTreeMap<QualifiedId<FunId>, bool>>,
    in_progress: RefCell<HashSet<QualifiedId<FunId>>>,
}

impl SpecPurityAnalysis {
    pub fn new() -> Box<Self> {
        Box::new(Self {
            function_purity_cache: RefCell::new(BTreeMap::new()),
            in_progress: RefCell::new(HashSet::new()),
        })
    }
    
    pub fn dump<W: std::io::Write>(&self, env: &GlobalEnv, targets: &FunctionTargetsHolder, writer: &mut W) -> std::io::Result<()> {
        writeln!(writer, "\n\n==== spec purity analysis result for vec_set module ====\n")?;
        
        let mut pure_count = 0;
        let mut impure_count = 0;
        let mut spec_impure_count = 0;
        let mut spec_impure_functions = Vec::new();
        
        // Iterate through all functions in the environment
        for module in env.get_modules() {
            let module_name = module.get_full_name_str();
            if !module_name.contains("vec_set") {
                continue;
            }

            for func in module.get_functions() {
                let func_id = func.get_qualified_id();
                
                let data_opt = targets.get_data(&func_id, &FunctionVariant::Baseline);
                if data_opt.is_none() {
                    continue;
                }
                
                let data = data_opt.unwrap();
                let purity_info = data.annotations.get::<PurityVerificationInfo>();
                
                if let Some(info) = purity_info {
                    let func_name = func.get_full_name_str();
                    writeln!(
                        writer,
                        "fun {} -> {}",
                        func_name,
                        if info.is_pure { "pure" } else { "impure" }
                    )?;
                    
                    if info.is_pure {
                        pure_count += 1;
                    } else {
                        impure_count += 1;
                        
                        if targets.is_spec(&func_id) {
                            spec_impure_count += 1;
                            spec_impure_functions.push(func_name.clone());
                            writeln!(writer, "  WARNING: This is a spec function with impure operations")?;
                        }
                        
                        let func_target = FunctionTarget::new(&func, &data);
                        let code = func_target.get_bytecode();
                        
                        writeln!(writer, "  Bytecode:")?;
                        for (idx, bc) in code.iter().enumerate() {
                            writeln!(writer, "    {}: {:?}", idx, bc)?;
                        }
                        
                        let modif_locations = self.find_modifiable_locations_in_function(
                            code, 
                            &func, 
                            targets, 
                            &func_target, 
                            &env, 
                            &None
                        );
                        
                        if !modif_locations.is_empty() {
                            writeln!(writer, "  Modified in:")?;
                            for loc in modif_locations {
                                // Get the source file name from the env
                                let file_id = loc.file_id();
                                let file_name = env.get_file(file_id).to_string_lossy();
                                // Get the source text for this location
                                let source = env.get_source(&loc);
                                writeln!(writer, "    - {}:{}-{} => {}", 
                                    file_name,
                                    loc.span().start(),
                                    loc.span().end(),
                                    source.unwrap_or("")
                                )?;
                            }
                        }
                    }
                }
            }
        }
        
        // Add summary section
        writeln!(writer, "\n==== Summary for vec_set module ====")?;
        writeln!(writer, "Total functions analyzed: {}", pure_count + impure_count)?;
        writeln!(writer, "Pure functions: {}", pure_count)?;
        writeln!(writer, "Impure functions: {}", impure_count)?;
        writeln!(writer, "Spec functions with impure operations: {}", spec_impure_count)?;
        
        // Add section for spec functions with impure operations
        if !spec_impure_functions.is_empty() {
            writeln!(writer, "\n==== Spec Functions with Impure Operations in vec_set module ====")?;
            for func_name in spec_impure_functions {
                writeln!(writer, "- {}", func_name)?;
            }
        }
        
        Ok(())
    }
    
    pub fn find_operation_in_function(&self, target_id: QualifiedId<FunId>, code: &[Bytecode]) -> Option<Operation> {
        for cp in code {
            match cp {
                Bytecode::Call(_, _, operation, _, _) => {
                    match operation {
                        Operation::Function(mod_id,fun_id, _) => {
                            let callee_id = mod_id.qualified(*fun_id);
                            if callee_id == target_id {
                                return Some(operation.clone());
                            }
                        },
                        _ => {}
                    };
                },
                _ => {},
            }
        }
        
        None
    }

    pub fn find_modifiable_locations_in_function(
        &self, 
        code: &[Bytecode], 
        func_env: &FunctionEnv,
        targets: &FunctionTargetsHolder,
        target: &FunctionTarget, 
        env: &GlobalEnv, 
        skip: &Option<Operation>,
    ) -> BTreeSet<Loc> {
        let mut results = BTreeSet::new();

        if !targets.is_spec(&func_env.get_qualified_id()) {
            for param in func_env.get_parameters() {
                if param.1.is_mutable_reference() {
                    results.insert(func_env.get_loc()); 
                }
            }
        }

        for cp in code {
            match cp {
                Bytecode::Call(attr, _, operation, _, _) => {
                    if skip.is_some() && skip.clone().unwrap() == *operation {
                        continue;
                    }
                    match operation {
                        Operation::Function(mod_id, func_id, _) => {
                            let module = env.get_module(*mod_id); 
                            let func = module.get_function(func_id.clone());

                            let bytecode_purity = self.recursive_bytecode_purity(env, &func);

                            if bytecode_purity {
                                continue;
                            }

                            let module_name = env.symbol_pool().string(module.get_name().name());

                            if module_name.as_str() == GlobalEnv::PROVER_MODULE_NAME || module_name.as_str() == GlobalEnv::SPEC_MODULE_NAME {
                                continue;
                            }

                            if RESTRICTED_MODULES.contains(&module_name.as_str()) {
                                results.insert(target.get_bytecode_loc(*attr)); 
                            }

                            let internal_data = targets.get_data(&mod_id.qualified(*func_id), &FunctionVariant::Baseline);
                            if internal_data.is_none() {
                                continue;
                            }
                                
                            let annotation = internal_data
                                .unwrap()
                                .annotations.get::<PurityVerificationInfo>()
                                .expect("Function expect to be already scanned");

                            if !annotation.is_pure {
                                results.insert(target.get_bytecode_loc(*attr)); 
                            }
                        },
                        _ => {}
                    };
                },
                _ => {},
            }
        }

        results
    }

    fn bytecode_purity(&self, bytecode:&[MoveBytecode]) -> bool {
        for bc in bytecode {
            match bc {
                MoveBytecode::MutBorrowLoc(_) |
                MoveBytecode::MutBorrowField(_) |
                MoveBytecode::MutBorrowFieldGeneric(_) |
                MoveBytecode::VecMutBorrow(_) |
                MoveBytecode::WriteRef |
                MoveBytecode::VecPushBack(_) |
                MoveBytecode::VecPopBack(_) |
                MoveBytecode::VecSwap(_) => {
                    return false;
                },
                _ => {}
            }
        }
        
        true
    }

    fn recursive_bytecode_purity(&self, env: &GlobalEnv, func: &FunctionEnv<'_>) -> bool {
        let func_id = func.get_qualified_id();
        
        if let Some(&result) = self.function_purity_cache.borrow().get(&func_id) {
            return result;
        }
        
        if self.in_progress.borrow().contains(&func_id) {
            return true;
        }
        
        self.in_progress.borrow_mut().insert(func_id);
        
        let generator = StacklessBytecodeGenerator::new(&func);
        let generated_data = generator.generate_function();
        let func_target = FunctionTarget::new(&func, &generated_data);
        
        if let Some(annotation) = func_target.get_annotations().get::<PurityVerificationInfo>() {
            if annotation.is_pure {
                self.function_purity_cache.borrow_mut().insert(func_id, true);
                self.in_progress.borrow_mut().remove(&func_id);
                return true;
            }
        }
        
        let generated_bytecode = func_target.get_bytecode();

        for cp in generated_bytecode {
            match cp {
                Bytecode::Call(_, _, operation, _, _) => {
                    match operation {
                        Operation::Function(mod_id, func_id, _) => {
                            let module = env.get_module(*mod_id); 
                            let new_func = module.get_function(func_id.clone());
                            let result = self.recursive_bytecode_purity(env, &new_func);
                            if !result {
                                self.function_purity_cache.borrow_mut().insert(func.get_qualified_id(), false);
                                self.in_progress.borrow_mut().remove(&func.get_qualified_id());
                                return false; 
                            }
                        }
                        _ => {},
                    }
                }, 
                _ => {},
            }
        }

        let func_bytecode: &[move_binary_format::file_format::Bytecode] = func.get_bytecode();
        let result = self.bytecode_purity(func_bytecode);
        
        self.function_purity_cache.borrow_mut().insert(func_id, result);
        self.in_progress.borrow_mut().remove(&func_id);
        
        result
    }

    fn analyse(&self, func_env: &FunctionEnv, targets: &FunctionTargetsHolder, data: &FunctionData) -> PurityVerificationInfo {
        let is_spec = targets.is_function_spec(&func_env.get_qualified_id());
        let env = func_env.module_env.env;
        let func_target = FunctionTarget::new(func_env, data);

        let underlying_func_id = targets.get_fun_by_spec(&func_env.get_qualified_id());

        let code = func_target.get_bytecode();

        let call_operation = if underlying_func_id.is_some() { self.find_operation_in_function(*underlying_func_id.unwrap(), code) } else { None };
        let modif_locations = self.find_modifiable_locations_in_function(code, &func_env, targets, &func_target, &env, &call_operation);

        if is_spec {
            for loc in modif_locations.iter() {
                env.diag(
                    Severity::Error,
                    loc,
                    "Consider removing non-pure calls form spec",
                );
            }
        }

        let result = PurityVerificationInfo { is_pure: modif_locations.len() == 0 };

        // let _ = self.dump_to_stdout(&env, targets);

        result
    }

    pub fn dump_to_stdout(&self, env: &GlobalEnv, targets: &FunctionTargetsHolder) -> std::io::Result<()> {
        let stdout = std::io::stdout();
        let mut writer = stdout.lock();
        self.dump(env, targets, &mut writer)
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
        let annotation = data
            .annotations
            .get::<PurityVerificationInfo>();

        let annotation_data = if annotation.is_some() { 
            annotation.unwrap().clone()
         } else { 
            self.analyse(func_env, targets, &data)
        };
    
        let fixedpoint = match scc_opt {
            None => true,
            Some(_) => match data.annotations.get::<PurityVerificationInfo>() {
                None => false,
                Some(old_annotation) => old_annotation.is_pure == annotation_data.is_pure
            },
        };

        data.annotations.set::<PurityVerificationInfo>(annotation_data, fixedpoint);

        data
    }

    fn name(&self) -> String {
        "spec_purity_analysis".to_string()
    }
}
