use codespan_reporting::diagnostic::Severity;
use move_model::{model::{FunId, FunctionEnv, GlobalEnv, QualifiedId}, ty::Type};

use crate::{
    deterministic_analysis, no_abort_analysis,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    stackless_bytecode::{AttrId, Bytecode, Operation, QuantifierType},
};

#[derive(Debug, Clone)]
pub struct QuantifierPattern {
    pub start_qid: QualifiedId<FunId>,
    pub end_qid: QualifiedId<FunId>,
    pub quantifier_type: QuantifierType,
}

impl QuantifierPattern {
    pub fn new(start_qid: QualifiedId<FunId>, end_qid: QualifiedId<FunId>, quantifier_type: QuantifierType) -> Self {
        Self {
            start_qid,
            end_qid,
            quantifier_type,
        }
    }

    pub fn all_patterns(env: &GlobalEnv) -> [QuantifierPattern; 11] {
        [
            QuantifierPattern::new(env.prover_begin_forall_lambda_qid(), env.prover_end_forall_lambda_qid(), QuantifierType::Forall),
            QuantifierPattern::new(env.prover_begin_exists_lambda_qid(), env.prover_end_exists_lambda_qid(), QuantifierType::Exists),
            QuantifierPattern::new(env.prover_begin_map_lambda_qid(), env.prover_end_map_lambda_qid(), QuantifierType::Map),
            QuantifierPattern::new(env.prover_begin_filter_lambda_qid(), env.prover_end_filter_lambda_qid(), QuantifierType::Filter),
            QuantifierPattern::new(env.prover_begin_find_lambda_qid(), env.prover_end_find_lambda_qid(), QuantifierType::Find),
            QuantifierPattern::new(env.prover_begin_find_index_lambda_qid(), env.prover_end_find_index_lambda_qid(), QuantifierType::FindIndex),
            QuantifierPattern::new(env.prover_begin_find_indices_lambda_qid(), env.prover_end_find_indices_lambda_qid(), QuantifierType::FindIndices),
            QuantifierPattern::new(env.prover_begin_sum_map_lambda_qid(), env.prover_end_sum_map_lambda_qid(), QuantifierType::SumMap),
            QuantifierPattern::new(env.prover_begin_count_lambda_qid(), env.prover_end_count_lambda_qid(), QuantifierType::Count),
            QuantifierPattern::new(env.prover_begin_any_lambda_qid(), env.prover_end_any_lambda_qid(), QuantifierType::Any),
            QuantifierPattern::new(env.prover_begin_all_lambda_qid(), env.prover_end_all_lambda_qid(), QuantifierType::All),
        ]
    }
}

pub struct QuantifierIteratorAnalysisProcessor();

impl QuantifierIteratorAnalysisProcessor {
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

    fn extract_call_attr_id(&self, bc: &Bytecode) -> AttrId {
        match bc {
            Bytecode::Call(attr_id, _, _, _, _) => {
                return *attr_id;
            },
            _ => {}
        };

        unreachable!("extract_call_attr_id should only be called with call bytecode")
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

    // filter out trace, load operations and index accesses
    fn filter_bc(&self, env: &GlobalEnv, bc: &Bytecode) -> bool {
        match bc {
            Bytecode::Load(_, _, _) => true,
            Bytecode::Call(_, _, op, _, _) => {
                match op {
                    // traces
                    Operation::TraceLocal(_)
                    | Operation::TraceExp(_, _)
                    | Operation::TraceGhost(_, _)
                    | Operation::TraceAbort
                    | Operation::TraceReturn(_)
                    | Operation::TraceGlobalMem(_)
                    | Operation::TraceMessage(_)
                    // struct props
                    | Operation::BorrowField(_,_,_,_)
                    | Operation::BorrowGlobal(_,_,_)
                    | Operation::GetField(_,_,_,_)
                    | Operation::GetGlobal(_,_,_)
                    => true,
                    Operation::Function(mod_id, fun_id, _) => {
                        let qid = mod_id.qualified(*fun_id);
                        // Filter out vector index access (borrow and borrow_mut)
                        env.std_vector_borrow_qid() == Some(qid)
                            || env.std_vector_borrow_mut_qid() == Some(qid)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    pub fn find_macro_patterns(&self, env: &GlobalEnv, targets: &FunctionTargetsHolder, pattern: &QuantifierPattern, all_bc: &Vec<Bytecode>) -> Vec<Bytecode> {
        let chain_len = 4;

        let bc = all_bc.iter().filter(|bc| !self.filter_bc(env, bc)).collect::<Vec<&Bytecode>>();

        if bc.len() < chain_len {
            return all_bc.to_vec();
        }

        for i in 0..bc.len() - (chain_len - 1) {
            if 
                self.is_searched_fn(&bc[i], pattern.start_qid) && // start function
                self.is_fn_call(&bc[i + 1]) && // actual function call
                self.is_destroy(&bc[i + 2]) && // destroy 
                self.is_searched_fn(&bc[i + 3], pattern.end_qid) // end function
            {
                let (start_attr_id, dests, srcs_vec, _, _) = self.extract_fn_call_data(&bc[i]);
                let (actual_call_attr_id, _, srcs_funcs, callee_id, type_params) = self.extract_fn_call_data(&bc[i + 1]);
                let destroy_attr_id = self.extract_call_attr_id(&bc[i + 2]);
                let (end_attr_id, dsts, _, _, _) = self.extract_fn_call_data(&bc[i + 3]);

                let lambda_index = match srcs_funcs.iter().position(|src| *src == dests[0]) {
                    Some(idx) => idx,
                    None => {
                        let callee_env = env.get_function(callee_id);
                        env.diag(
                            Severity::Error,
                            &callee_env.get_loc(),
                            "Invalid quantifier macro pattern: lambda parameter not found in function call arguments",
                        );
                        return all_bc.to_vec();
                    }
                };

                if self.validate_function_pattern_requirements(env, targets, callee_id) {
                    return all_bc.to_vec();
                }

                let mut new_bc = all_bc.clone();
                let new_bc_el = Bytecode::Call(
                    actual_call_attr_id,
                    dsts,
                    Operation::Quantifier(pattern.quantifier_type, callee_id, type_params, lambda_index),
                    // for forall and exists it will be [] otherwise [v]
                    srcs_vec.into_iter().chain(srcs_funcs.into_iter()).collect(),
                    None
                );

                new_bc.retain(|bytecode| {
                    if let Bytecode::Call(aid, ..) = bytecode {
                        *aid != start_attr_id && *aid != destroy_attr_id && *aid != end_attr_id
                    } else {
                        true
                    }
                });
                
                if let Some(pos) = new_bc.iter().position(|bytecode| {
                    if let Bytecode::Call(aid, ..) = bytecode {
                        *aid == actual_call_attr_id
                    } else {
                        false
                    }
                }) {
                    new_bc[pos] = new_bc_el;
                }

                // recursively search for more macro of this type
                return self.find_macro_patterns(env, targets, pattern, &new_bc);
            } else if self.is_searched_fn(&bc[i], pattern.start_qid) {
                let callee_env = env.get_function(pattern.start_qid);
                env.diag(
                    Severity::Error,
                    &callee_env.get_loc(),
                    "Invalid quantifier macro pattern: Invalid standalone usage of start function",
                );

                return all_bc.to_vec();
            } else if self.is_searched_fn(&bc[i], pattern.end_qid) {
                let callee_env = env.get_function(pattern.end_qid);

                env.diag(
                    Severity::Error,
                    &callee_env.get_loc(),
                    "Invalid quantifier macro pattern: Invalid standalone usage of end function",
                );

                return all_bc.to_vec();
            }
        }

        all_bc.to_vec()
    }
}

impl FunctionTargetProcessor for QuantifierIteratorAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        let env = func_env.module_env.env;
        let func_target = FunctionTarget::new(func_env, &data);
        let code = func_target.get_bytecode();

        let patterns = QuantifierPattern::all_patterns(env);

        let mut bc = code.to_vec();

        for pattern in &patterns {
            bc = self.find_macro_patterns(env, &targets, pattern, &bc);
        }

        let mut data = data.clone();
        data.code = bc;

        data
    }

    fn name(&self) -> String {
        "quantifier_iterator_analysis".to_string()
    }
}
