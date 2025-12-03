use codespan_reporting::diagnostic::Severity;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, ModuleId, QualifiedId};
use std::collections::BTreeMap;

use crate::{
    deterministic_analysis,
    function_data_builder::FunctionDataBuilder,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
};

pub struct PureFunctionAnalysisProcessor();

impl PureFunctionAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    pub fn special_pure_functions_map(env: &GlobalEnv) -> BTreeMap<QualifiedId<FunId>, String> {
        let mut special_funcs = BTreeMap::new();
        special_funcs.insert(env.std_vector_borrow_qid().unwrap(), "ReadVec".to_string());
        special_funcs
    }

    fn check_function(
        &self,
        mid: ModuleId,
        fid: FunId,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> Option<String> {
        let qid = mid.qualified(fid);
        let func_env = env.get_function(qid);
        if func_env.is_native()
            || targets.is_pure_fun(&func_env.get_qualified_id())
            || env.should_be_used_as_func(&qid)
            || Self::special_pure_functions_map(env).contains_key(&qid)
        {
            return None;
        } else {
            return Some(format!(
                "Function '{}' can't be used in pure functions.{}",
                func_env.get_full_name_str(),
                if func_env.module_env.is_target() {
                    " Try marking it with #[ext(pure)] attribute."
                } else {
                    ""
                },
            ));
        }
    }

    fn check_parameters(&self, func_env: &FunctionEnv) -> bool {
        for param in func_env.get_parameters() {
            if param.1.is_mutable_reference() {
                func_env.module_env.env.diag(
                    Severity::Error,
                    &func_env.get_loc(),
                    &format!(
                        "Pure functions cannot have mutable reference parameters: '{}'",
                        func_env.symbol_pool().string(param.0)
                    ),
                );
                return false;
            }
        }

        if func_env.get_return_count() != 1 {
            func_env.module_env.env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Pure functions must have exactly one return value",
            );
            return false;
        }

        true
    }
}

impl FunctionTargetProcessor for PureFunctionAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !targets.is_pure_fun(&fun_env.get_qualified_id()) {
            return data;
        }

        if !self.check_parameters(fun_env) {
            return data;
        }

        if !deterministic_analysis::get_info(&data).is_deterministic {
            fun_env.module_env.env.diag(
                Severity::Error,
                &fun_env.get_loc(),
                &format!(
                    "Pure function '{}' must be deterministic",
                    fun_env.get_full_name_str()
                ),
            );
            return data;
        }

        let mut builder = FunctionDataBuilder::new(fun_env, data);
        let code = std::mem::take(&mut builder.data.code);
        for bc in code.iter() {
            builder.emit(bc.update_abort_action(|f| None).replace_cast_with_assign());
        }

        // Check if a bytecode instruction can be emitted in a Boogie function (straightline code).
        // Control flow instructions (jumps, branches, labels) are silently skipped since
        // if_then_else expressions have already summarized their effects.
        for bc in builder.data.code.iter() {
            use Bytecode::*;
            let error = match bc {
                Assign(_, _, _, _) => None,
                Load(_, _, _) => None,
                Call(_, _, op, _, _) => match op {
                    Operation::Quantifier(_, _, _, _) => {
                        Some("Quantifiers not allowed in pure functions yet".to_string())
                    }
                    Operation::Function(mid, fid, _) => {
                        self.check_function(*mid, *fid, fun_env.module_env.env, &targets)
                    }
                    _ => None,
                },
                Ret(_, _) => None,
                Nop(_) => None,
                Jump(_, _) => None,
                Branch(_, _, _, _) => None,
                Label(_, _) => None,
                VariantSwitch(_, _, _) => {
                    Some("Pure functions cannot have variant switch operations".to_string())
                }
                Abort(_, _) => Some("Pure functions cannot abort".to_string()),
                // should be unreachable
                SaveMem(_, _, _) => {
                    Some("Pure functions cannot use memory save operations".to_string())
                }
                Prop(_, _, _) => {
                    Some("Pure functions cannot have specification properties".to_string())
                }
            };
            if let Some(reason) = error {
                fun_env.module_env.env.diag(
                    Severity::Error,
                    &builder.get_loc(bc.get_attr_id()),
                    &reason,
                );
                return builder.data;
            }
        }

        builder.data
    }

    fn name(&self) -> String {
        "pure_function_analysis".to_string()
    }
}
