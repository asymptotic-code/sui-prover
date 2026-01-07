use codespan_reporting::diagnostic::Severity;
use move_model::{
    model::{FunId, FunctionEnv, GlobalEnv, QualifiedId},
    ty::Type,
};

use crate::{
    deterministic_analysis,
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
    pub fn new(
        start_qid: QualifiedId<FunId>,
        end_qid: QualifiedId<FunId>,
        quantifier_type: QuantifierType,
    ) -> Self {
        Self {
            start_qid,
            end_qid,
            quantifier_type,
        }
    }

    pub fn all_patterns(env: &GlobalEnv) -> [QuantifierPattern; 21] {
        [
            QuantifierPattern::new(
                env.prover_begin_forall_lambda_qid(),
                env.prover_end_forall_lambda_qid(),
                QuantifierType::Forall,
            ),
            QuantifierPattern::new(
                env.prover_begin_exists_lambda_qid(),
                env.prover_end_exists_lambda_qid(),
                QuantifierType::Exists,
            ),
            QuantifierPattern::new(
                env.prover_begin_map_lambda_qid(),
                env.prover_end_map_lambda_qid(),
                QuantifierType::Map,
            ),
            QuantifierPattern::new(
                env.prover_begin_map_range_lambda_qid(),
                env.prover_end_map_lambda_qid(),
                QuantifierType::MapRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_filter_lambda_qid(),
                env.prover_end_filter_lambda_qid(),
                QuantifierType::Filter,
            ),
            QuantifierPattern::new(
                env.prover_begin_filter_range_lambda_qid(),
                env.prover_end_filter_lambda_qid(),
                QuantifierType::FilterRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_find_lambda_qid(),
                env.prover_end_find_lambda_qid(),
                QuantifierType::Find,
            ),
            QuantifierPattern::new(
                env.prover_begin_find_range_lambda_qid(),
                env.prover_end_find_lambda_qid(),
                QuantifierType::FindRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_find_index_lambda_qid(),
                env.prover_end_find_index_lambda_qid(),
                QuantifierType::FindIndex,
            ),
            QuantifierPattern::new(
                env.prover_begin_find_index_range_lambda_qid(),
                env.prover_end_find_index_lambda_qid(),
                QuantifierType::FindIndexRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_find_indices_lambda_qid(),
                env.prover_end_find_indices_lambda_qid(),
                QuantifierType::FindIndices,
            ),
            QuantifierPattern::new(
                env.prover_begin_find_indices_range_lambda_qid(),
                env.prover_end_find_indices_lambda_qid(),
                QuantifierType::FindIndicesRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_sum_map_lambda_qid(),
                env.prover_end_sum_map_lambda_qid(),
                QuantifierType::SumMap,
            ),
            QuantifierPattern::new(
                env.prover_begin_sum_map_range_lambda_qid(),
                env.prover_end_sum_map_lambda_qid(),
                QuantifierType::SumMapRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_count_lambda_qid(),
                env.prover_end_count_lambda_qid(),
                QuantifierType::Count,
            ),
            QuantifierPattern::new(
                env.prover_begin_count_range_lambda_qid(),
                env.prover_end_count_lambda_qid(),
                QuantifierType::CountRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_any_lambda_qid(),
                env.prover_end_any_lambda_qid(),
                QuantifierType::Any,
            ),
            QuantifierPattern::new(
                env.prover_begin_any_range_lambda_qid(),
                env.prover_end_any_lambda_qid(),
                QuantifierType::AnyRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_all_lambda_qid(),
                env.prover_end_all_lambda_qid(),
                QuantifierType::All,
            ),
            QuantifierPattern::new(
                env.prover_begin_all_range_lambda_qid(),
                env.prover_end_all_lambda_qid(),
                QuantifierType::AllRange,
            ),
            QuantifierPattern::new(
                env.prover_begin_range_map_lambda_qid(),
                env.prover_end_range_map_lambda_qid(),
                QuantifierType::RangeMap,
            ),
        ]
    }

    pub fn type_from_qid(qid: QualifiedId<FunId>, env: &GlobalEnv) -> Option<QuantifierType> {
        Self::all_patterns(env)
            .iter()
            .find(|p| qid == p.start_qid || qid == p.end_qid)
            .map(|p| p.quantifier_type)
    }
}

pub struct QuantifierIteratorAnalysisProcessor();

impl QuantifierIteratorAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn extract_fn_call_data(
        &self,
        bc: &Bytecode,
    ) -> (
        AttrId,
        Vec<usize>,
        Vec<usize>,
        QualifiedId<FunId>,
        Vec<Type>,
    ) {
        match bc {
            Bytecode::Call(attr_id, dsts, operation, srcs, _abort_action) => {
                if let Operation::Function(mod_id, fun_id, type_params) = operation {
                    let callee_id = mod_id.qualified(*fun_id);
                    return (
                        attr_id.clone(),
                        dsts.clone(),
                        srcs.clone(),
                        callee_id,
                        type_params.clone(),
                    );
                }
            }
            _ => {}
        };

        unreachable!("extract_fn_call_data should only be called with function call bytecode")
    }

    fn extract_call_attr_id(&self, bc: &Bytecode) -> AttrId {
        match bc {
            Bytecode::Call(attr_id, _, _, _, _) => {
                return *attr_id;
            }
            _ => {}
        };

        unreachable!("extract_call_attr_id should only be called with call bytecode")
    }

    fn is_fn_call(&self, bc: &Bytecode) -> bool {
        match bc {
            Bytecode::Call(_, _, operation, _, _) => match operation {
                Operation::Function(_, _, _) => true,
                _ => false,
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
            Bytecode::Call(_, _, operation, _, _) => match operation {
                Operation::Function(mod_id, fun_id, _) => qid == mod_id.qualified(*fun_id),
                _ => false,
            },
            _ => false,
        }
    }

    fn validate_function_pattern_requirements(
        &self,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        qid: QualifiedId<FunId>,
    ) -> bool {
        let func_env = env.get_function(qid);

        // Allow native functions (they are assumed to be pure)
        if func_env.is_native() {
            return false;
        }

        let data = targets.get_data(&qid, &FunctionVariant::Baseline).unwrap();

        // NOTE: workaround for issue #329: nested quantifiers are not supported yet, so we allow extra bpl with no_abort attribute
        if !targets.is_function_with_abort_check(&qid) {
            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Quantifier function should be pure ",
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

    fn filter_traces(&self, bc: &Bytecode) -> bool {
        match bc {
            Bytecode::Call(_, _, op, _, _) => {
                match op {
                    // traces
                    Operation::TraceLocal(_)
                    | Operation::TraceExp(_, _)
                    | Operation::TraceGhost(_, _)
                    | Operation::TraceAbort
                    | Operation::TraceReturn(_)
                    | Operation::TraceGlobalMem(_)
                    | Operation::TraceMessage(_) => true,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn get_start_func_pos_before(
        &self,
        bc: &Vec<&Bytecode>,
        start_qid: QualifiedId<FunId>,
        index: usize,
    ) -> Option<usize> {
        if index == 0 {
            return None;
        }

        for i in (0..index).rev() {
            if self.is_searched_fn(bc[i], start_qid) {
                return Some(i);
            }
        }

        None
    }

    fn find_lambda_variable_uses(
        &self,
        bc: &Vec<&Bytecode>,
        temp_var: usize,
        start_idx: usize,
        end_idx: usize,
    ) -> Vec<AttrId> {
        let mut findings = vec![];
        for i in start_idx..end_idx {
            if let Bytecode::Call(attr_id, _, _, srcs, _) = bc[i] {
                if srcs.contains(&temp_var) {
                    findings.push(attr_id.clone());
                }
            }
        }

        findings
    }

    pub fn find_macro_patterns(
        &self,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        target: &FunctionTarget,
        pattern: &QuantifierPattern,
        all_bc: &Vec<Bytecode>,
    ) -> (Vec<Bytecode>, bool) {
        let chain_len = 4;

        let bc = all_bc
            .iter()
            .filter(|bc| !self.filter_traces(bc))
            .collect::<Vec<&Bytecode>>();

        if bc.len() < chain_len {
            return (all_bc.to_vec(), false);
        }

        for i in 0..bc.len() - 2 {
            if self.is_fn_call(&bc[i]) // actual function call
                && self.is_destroy(&bc[i + 1]) // destroy 
                && self.is_searched_fn(&bc[i + 2], pattern.end_qid) // end function
                && self.get_start_func_pos_before(&bc, pattern.start_qid, i).is_some()
            // search for start fun
            {
                let start_idx = self
                    .get_start_func_pos_before(&bc, pattern.start_qid, i)
                    .unwrap();
                let (start_attr_id, dests, srcs_vec, _, _) =
                    self.extract_fn_call_data(&bc[start_idx]);
                let (actual_call_attr_id, _, srcs_funcs, callee_id, type_params) =
                    self.extract_fn_call_data(&bc[i]);
                let destroy_attr_id = self.extract_call_attr_id(&bc[i + 1]);
                let (end_attr_id, dsts, _, _, _) = self.extract_fn_call_data(&bc[i + 2]);

                // NOTE: dests[0] -> is produced "X" lambda variable

                let restricted_usages = self.find_lambda_variable_uses(&bc, dests[0], start_idx, i);
                for attr in &restricted_usages {
                    env.diag(
                        Severity::Error,
                        &target.get_bytecode_loc(*attr),
                        "Invalid quantifier macro pattern: lambda parameter is used externally",
                    );
                }

                if !restricted_usages.is_empty() {
                    return (all_bc.clone(), true);
                }

                let lambda_index = match srcs_funcs.iter().position(|src| *src == dests[0]) {
                    Some(idx) => idx,
                    None => {
                        let callee_env = env.get_function(callee_id);
                        env.diag(
                            Severity::Error,
                            &callee_env.get_loc(),
                            "Invalid quantifier macro pattern: lambda parameter not found in function call arguments",
                        );
                        return (all_bc.to_vec(), true);
                    }
                };

                if self.validate_function_pattern_requirements(env, targets, callee_id) {
                    return (all_bc.to_vec(), true);
                }

                let mut new_bc = all_bc.clone();
                let new_bc_el = Bytecode::Call(
                    actual_call_attr_id,
                    dsts,
                    Operation::Quantifier(
                        pattern.quantifier_type,
                        callee_id,
                        type_params,
                        lambda_index,
                    ),
                    // for forall and exists it will be [] otherwise [v]
                    srcs_vec.into_iter().chain(srcs_funcs.into_iter()).collect(),
                    None,
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
                return self.find_macro_patterns(env, targets, target, pattern, &new_bc);
            }
        }

        (all_bc.to_vec(), false)
    }

    fn scan_for_broken_patterns(
        &self,
        patterns: &Vec<QuantifierPattern>,
        func_env: &FunctionEnv,
        bc: &Vec<Bytecode>,
    ) {
        for pattern in patterns {
            for i in 0..bc.len() {
                if self.is_searched_fn(&bc[i], pattern.start_qid)
                    || self.is_searched_fn(&bc[i], pattern.end_qid)
                {
                    func_env.module_env.env.diag(
                        Severity::Error,
                        &func_env.get_loc(),
                        "Invalid quantifier macro pattern: expected a lambda function, but found an inlined expression",
                    );
                    return;
                }
            }
        }
    }
}

impl FunctionTargetProcessor for QuantifierIteratorAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        mut data: FunctionData,
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
            let (new_bc, is_error) =
                self.find_macro_patterns(env, &targets, &func_target, pattern, &bc);
            bc = new_bc;
            if is_error {
                return data;
            }
        }

        self.scan_for_broken_patterns(&patterns.to_vec(), func_env, &bc);

        data.code = bc;
        data
    }

    fn name(&self) -> String {
        "quantifier_iterator_analysis".to_string()
    }
}
