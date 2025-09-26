use std::collections::BTreeSet;
use codespan_reporting::diagnostic::Severity;
use move_model::{model::{FunId, FunctionEnv, GlobalEnv, Loc, QualifiedId}, symbol::Symbol, ty::Type};

use crate::{
    deterministic_analysis, function_data_builder::FunctionDataBuilder, function_target::{FunctionData, FunctionTarget}, function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant}, no_abort_analysis, stackless_bytecode::{AttrId, Bytecode, Operation, QuantifierType}, stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph}
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
                "Quantififier function should not abort",
            );

            return true;
        }

        if !deterministic_analysis::get_info(data).is_deterministic {
            env.diag(
                Severity::Error,
                &func_env.get_loc(),
                "Quantififier function should be deterministic",
            );

            return true;
        }

        // probably other check in future
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
                let (attr_id, _, srcs, callee_id, type_params) = self.extract_fn_call_data(&bc[i + 2]);
                let (_, dsts, _, _, _) = self.extract_fn_call_data(&bc[i + 4]);

                if self.validate_function_pattern_requirements(env, targets, callee_id) {
                    return bc.to_vec();
                }

                let mut new_bc = bc.clone();
                let new_bc_el = Bytecode::Call(
                    attr_id,
                    dsts,
                    Operation::Quantifier(quantifier, callee_id, type_params),
                    srcs,
                    None
                );

                new_bc.splice(i..=i + (chain_len - 1), [new_bc_el]);

                // recursively search for more macro of this type
                return self.find_macro_patterns(env, targets, start_qid, end_qid, quantifier, &new_bc);
            }
        }

        bc.to_vec()
    }

    pub fn find_node_operation(&self, block_id: BlockId, cfg: &StacklessControlFlowGraph, code: &[Bytecode], targets: &[Operation], builder: &FunctionDataBuilder) -> Option<Loc> {
        match cfg.content(block_id) {
            BlockContent::Dummy => {},
            BlockContent::Basic { lower, upper } => {
                for position in *lower..*upper {
                    match &code[position as usize] {
                        Bytecode::Call(attr, _, opr, _, _) => {
                            if targets.contains(opr) {
                                return Some(builder.get_loc(*attr));
                            }
                        },
                        _ => {},
                    }
                }
            }
        }
    
        return None;
    }

    pub fn find_operations_before_after_operation_in_node(&self, block_id: &BlockId, operation: &Operation, cfg: &StacklessControlFlowGraph, code: &[Bytecode], builder: &FunctionDataBuilder, preconditions: &[Operation], postconditions: &[Operation]) -> (BTreeSet<Loc>, BTreeSet<Loc>) {
        let mut befores = BTreeSet::new();
        let mut afters = BTreeSet::new();
        let mut matched = false;

        match cfg.content(*block_id) {
            BlockContent::Dummy => {},
            BlockContent::Basic { lower, upper } => {
                for position in *lower..*upper {
                    match &code[position as usize] {
                        Bytecode::Call(attr, _, opr, _, _) => {
                            if opr == operation {
                                matched = true;
                            }

                            if !matched && postconditions.contains(opr) {
                                befores.insert(builder.get_loc(*attr));
                            }

                            if matched && preconditions.contains(opr) {
                                afters.insert(builder.get_loc(*attr));
                            }
                        },
                        _ => {},
                    }
                }
            }
        }
    
        return (afters, befores);
    }

    pub fn get_return_variables(&self, func_env: &FunctionEnv, code: &[Bytecode]) -> Vec<Vec<Symbol>> {
        // using matrix to cover all possible returns with params
        let mut results = vec!();
        for cp in code.iter() {
            match cp {
                Bytecode::Ret(_, srcs) => {
                    let mut result: Vec<Symbol> = vec!();
                    for idx in srcs.clone() {
                        let lc = func_env.get_local_name(idx);
                        result.push(lc);
                    }
                    
                    results.push(result);
                } 
                _ => {}
            }
        }

        results
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
