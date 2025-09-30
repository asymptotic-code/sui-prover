use codespan_reporting::diagnostic::Severity;
use move_model::{model::{FunId, FunctionEnv, GlobalEnv, QualifiedId}, ty::Type};

use crate::{
    deterministic_analysis, no_abort_analysis,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{AttrId, Bytecode, Operation, QuantifierType},
};

pub struct MacroQuantifiersAnalysisProcessor();

impl MacroQuantifiersAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn extract_fn_call_data(&self, bc: &Bytecode) -> (AttrId, Vec<usize>, Vec<usize>, QualifiedId<FunId>, Vec<Type>) {
        match bc {
            Bytecode::Call(attr_id, dsts, operation, srcs, _abort_action) => {
                if let Operation::Function(mod_id, fun_id, type_params) = operation {
                    let callee_id = mod_id.qualified(*fun_id);
                    return (attr_id.clone(), dsts.clone(), srcs.clone(), callee_id, type_params.clone());
                }
            },
            _ => {}
        };

        unreachable!("extract_fn_call_data should only be called with function call bytecode")
    }

    fn is_fn_call(&self, bc: &Bytecode) -> bool {
        match bc {
            Bytecode::Call(_, _, operation, _, _) => {
                match operation {
                    Operation::Function(_,_, _) => true,
                    _ => false
                }
            },
            _ => false,
        }
    }

    fn is_destroy(&self, bc: &Bytecode) -> bool {
        match bc {
            Bytecode::Call(_, _, op, _, _) => matches!(op, Operation::Destroy),
            _ => false,
        }
    }

    fn is_trace_local(&self, bc: &Bytecode) -> bool {
        match bc {
            Bytecode::Call(_, _, op, _, _) => matches!(op, Operation::TraceLocal(_)),
            _ => false,
        }
    }

    fn is_searched_fn(&self, bc: &Bytecode, qid: QualifiedId<FunId>) -> bool {
        match bc {
            Bytecode::Call(_, _, operation, _, _) => {
                match operation {
                    Operation::Function(mod_id,fun_id, _) => {
                        qid == mod_id.qualified(*fun_id)
                    },
                    _ => false
                }
            },
            _ => false,
        }
    }

    fn validate_function_pattern_requirements(&self, env: &GlobalEnv, targets: &FunctionTargetsHolder, qid: QualifiedId<FunId>) -> bool {
        let func_env = env.get_function(qid);
        let data = targets.get_data(&qid, &FunctionVariant::Baseline).unwrap();

        if !no_abort_analysis::get_info(data).does_not_abort && !targets.is_abort_check_fun(&qid) {
            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Quantifier function should not abort",
            );

            return true;
        }

        if !deterministic_analysis::get_info(data).is_deterministic {
            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Quantifier function should be deterministic",
            );

            return true;
        }

        return false;
    }

    pub fn find_macro_patterns(&self, env: &GlobalEnv, targets: &FunctionTargetsHolder, start_qid: QualifiedId<FunId>, end_qid: QualifiedId<FunId>, quantifier: QuantifierType, bc: &Vec<Bytecode>) -> Vec<Bytecode> {
        let chain_len = 5;
        if bc.len() < chain_len {
            return bc.to_vec();
        }

        for i in 0..bc.len() - (chain_len - 1) {
            if 
                self.is_searched_fn(&bc[i], start_qid) &&
                self.is_trace_local(&bc[i + 1]) &&
                self.is_fn_call(&bc[i + 2]) && 
                self.is_destroy(&bc[i + 3]) &&
                self.is_searched_fn(&bc[i + 4], end_qid) 
            {
                let (attr_id, _, srcs_base, callee_id, type_params) = self.extract_fn_call_data(&bc[i + 2]);
                let (_, _, srcs_vec, _, _) = self.extract_fn_call_data(&bc[i]);
                let (_, dsts, _, _, _) = self.extract_fn_call_data(&bc[i + 4]);

                if self.validate_function_pattern_requirements(env, targets, callee_id) {
                    return bc.to_vec();
                }

                let mut new_bc = bc.clone();
                let new_bc_el = Bytecode::Call(
                    attr_id,
                    dsts,
                    Operation::Quantifier(quantifier, callee_id, type_params),
                    if srcs_vec.len() > 0 { srcs_vec } else { srcs_base },
                    None
                );

                new_bc.splice(i..=i + (chain_len - 1), [new_bc_el]);

                // recursively search for more macro of this type
                return self.find_macro_patterns(env, targets, start_qid, end_qid, quantifier, &new_bc);
            } else if self.is_searched_fn(&bc[i], start_qid) {
                let calle_env = env.get_function(start_qid);
                env.diag(
                    Severity::Error,
                    &calle_env.get_loc(),
                    "Invalid quantifier macro pattern: Invalid standalone usage of start function",
                );

                return bc.to_vec();
            } else if self.is_searched_fn(&bc[i], end_qid) {
                let calle_env = env.get_function(end_qid);

                env.diag(
                    Severity::Error,
                    &calle_env.get_loc(),
                    "Invalid quantifier macro pattern: Invalid standalone usage of end function",
                );

                return bc.to_vec();
            }
        }

        bc.to_vec()
    }
}

impl FunctionTargetProcessor for MacroQuantifiersAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !targets.is_spec(&func_env.get_qualified_id()) {
            return data;
        }

        let env = func_env.module_env.env;
        let func_target = FunctionTarget::new(func_env, &data);
        let code = func_target.get_bytecode();

        // start, end, replace
        let conditions = [
            (env.prover_begin_forall_lambda_qid(), env.prover_end_forall_lambda_qid(), QuantifierType::Forall),
            (env.prover_begin_exists_lambda_qid(), env.prover_end_exists_lambda_qid(), QuantifierType::Exists),

            (env.prover_begin_map_lambda_qid(), env.prover_end_map_lambda_qid(), QuantifierType::Map),
            (env.prover_begin_filter_lambda_qid(), env.prover_end_filter_lambda_qid(), QuantifierType::Filter),
            (env.prover_begin_find_lambda_qid(), env.prover_end_find_lambda_qid(), QuantifierType::Find),
            (env.prover_begin_find_index_lambda_qid(), env.prover_end_find_index_lambda_qid(), QuantifierType::FindIndex),
            (env.prover_begin_find_indices_lambda_qid(), env.prover_end_find_indices_lambda_qid(), QuantifierType::FindIndices),
            (env.prover_begin_sum_map_lambda_qid(), env.prover_end_sum_map_lambda_qid(), QuantifierType::SumMap),
            (env.prover_begin_count_lambda_qid(), env.prover_end_count_lambda_qid(), QuantifierType::Count),
            (env.prover_begin_any_lambda_qid(), env.prover_end_any_lambda_qid(), QuantifierType::Any),
            (env.prover_begin_all_lambda_qid(), env.prover_end_all_lambda_qid(), QuantifierType::All),
        ];

        let mut bc = code.to_vec();

        for ac in conditions {
            bc = self.find_macro_patterns(env, &targets, ac.0, ac.1, ac.2, &bc);
        }

        let mut data = data.clone();
        data.code = bc;

        data
    }

    fn name(&self) -> String {
        "macro_quantifiers_analysis".to_string()
    }
}
