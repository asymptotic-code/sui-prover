use codespan_reporting::diagnostic::Severity;
use move_model::model::{FunId, FunctionEnv, GlobalEnv, ModuleId, QualifiedId};
use std::collections::BTreeSet;

use crate::{
    deterministic_analysis,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
};

pub struct PureFunctionAnalysisProcessor();

impl PureFunctionAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    pub fn native_pure_variants(env: &GlobalEnv) -> BTreeSet<QualifiedId<FunId>> {
        BTreeSet::from([
            env.std_vector_borrow_qid().unwrap(),
            env.table_borrow_qid().unwrap(),
            env.object_table_borrow_qid().unwrap(),
            env.dynamic_field_borrow_qid().unwrap(),
            env.dynamic_object_field_borrow_qid().unwrap(),
        ])
    }

    fn check_function(
        mid: ModuleId,
        fid: FunId,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
    ) -> Option<String> {
        let qid = mid.qualified(fid);
        let func_env = env.get_function(qid);
        if targets.is_pure_fun(&func_env.get_qualified_id())
            || targets.is_pure_callee(&func_env.get_qualified_id())
            || env.should_be_used_as_func(&qid)
            || Self::native_pure_variants(env).contains(&qid)
        {
            return None;
        }
        Some(format!(
            "Function '{}' can't be used in pure functions.{}",
            func_env.get_full_name_str(),
            if func_env.module_env.is_target() {
                " Try marking it with #[ext(pure)] attribute."
            } else {
                ""
            },
        ))
    }

    // Check if a bytecode instruction can be emitted in a Boogie function (straightline code).
    // Control flow instructions (jumps, branches, labels) are silently skipped since
    // if_then_else expressions have already summarized their effects.
    pub fn check_bytecode(
        fun_env: &FunctionEnv,
        data: &FunctionData,
        targets: &FunctionTargetsHolder,
        is_callee: bool,
    ) -> Option<(move_model::model::Loc, String)> {
        let prefix = if is_callee {
            format!(
                "Function '{}' called from a pure function",
                fun_env.get_full_name_str()
            )
        } else {
            "Pure functions".to_string()
        };
        for bc in data.code.iter() {
            use Bytecode::*;
            let error = match bc {
                Assign(_, _, _, _) => None,
                Load(_, _, _) => None,
                Call(_, _, op, _, _) => match op {
                    Operation::Function(mid, fid, _) => {
                        Self::check_function(*mid, *fid, fun_env.module_env.env, targets)
                    }
                    _ => None,
                },
                Ret(_, _) => None,
                Nop(_) => None,
                Jump(_, _) => None,
                Branch(_, _, _, _) => None,
                Label(_, _) => None,
                VariantSwitch(_, _, _) => {
                    Some(format!("{prefix} cannot have variant switch operations"))
                }
                Abort(_, _) => Some(format!("{prefix} cannot abort")),
                // should be unreachable
                SaveMem(_, _, _) => Some(format!("{prefix} cannot use memory save operations")),
                Prop(_, _, _) => Some(format!("{prefix} cannot have specification properties")),
            };
            if let Some(reason) = error {
                let loc = data
                    .locations
                    .get(&bc.get_attr_id())
                    .cloned()
                    .unwrap_or_else(|| fun_env.get_loc());
                return Some((loc, reason));
            }
        }

        None
    }

    fn check_parameters(func_env: &FunctionEnv, is_callee: bool) -> bool {
        for param in func_env.get_parameters() {
            if param.1.is_mutable_reference() {
                let msg = if is_callee {
                    format!(
                        "Function '{}' called from a pure function has mutable reference parameter: '{}'",
                        func_env.get_full_name_str(),
                        func_env.symbol_pool().string(param.0)
                    )
                } else {
                    format!(
                        "Pure functions cannot have mutable reference parameters: '{}'",
                        func_env.symbol_pool().string(param.0)
                    )
                };
                func_env
                    .module_env
                    .env
                    .diag(Severity::Error, &func_env.get_loc(), &msg);
                return false;
            }
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
        let qid = fun_env.get_qualified_id();

        let is_callee = targets.is_pure_callee(&qid);

        if !targets.is_pure_fun(&qid) && !is_callee {
            return data;
        }

        if !Self::check_parameters(fun_env, is_callee) {
            return data;
        }

        if !deterministic_analysis::get_info(&data).is_deterministic {
            let msg = if is_callee {
                format!(
                    "Function '{}' called from a pure function must be deterministic",
                    fun_env.get_full_name_str()
                )
            } else {
                format!(
                    "Pure function '{}' must be deterministic",
                    fun_env.get_full_name_str()
                )
            };
            fun_env
                .module_env
                .env
                .diag(Severity::Error, &fun_env.get_loc(), &msg);
            return data;
        }

        if let Some((loc, reason)) = Self::check_bytecode(fun_env, &data, targets, is_callee) {
            fun_env.module_env.env.diag(Severity::Error, &loc, &reason);
            return data;
        }

        data
    }

    fn name(&self) -> String {
        "pure_function_analysis".to_string()
    }
}
