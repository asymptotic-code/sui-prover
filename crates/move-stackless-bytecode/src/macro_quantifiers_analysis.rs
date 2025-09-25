use std::collections::BTreeSet;
use move_model::{model::{FunId, FunctionEnv, Loc, QualifiedId}, symbol::Symbol};

use crate::{
    function_data_builder::FunctionDataBuilder, function_target::{FunctionData, FunctionTarget}, function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder}, stackless_bytecode::{Bytecode, Operation, QuantifierType}, stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph}
};

pub struct MacroQuantifiersAnalysisProcessor();

impl MacroQuantifiersAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn extract_fn_call_data(self, bc: &Bytecode) -> (Vec<usize>, Vec<usize>, QualifiedId<FunId>, Vec<Type>) {
        match bc {
            Bytecode::Call(_attr_id, dsts, operation, srcs, _abort_action) => {
                if let Operation::Function(mod_id, fun_id, type_params) = operation {
                    let callee_id = mod_id.qualified(*fun_id);
                    return (dsts.clone(), srcs.clone(), callee_id, type_params.clone());
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

    pub fn find_node_by_func_id(&self, start_qid: QualifiedId<FunId>, end_qid: QualifiedId<FunId>, quantifier: QuantifierType, bc: &[Bytecode]) {
        let mut multiple = false;
        let mut result = None;

        for i in 0..bc.len() - 2 {
            if self.is_searched_fn(&bc[i], start_qid) && self.is_fn_call(&bc[i + 1]) && self.is_searched_fn(&bc[i + 2], start_qid) {
                let (dsts, srcs, callee_id, type_params) = self.extract_fn_call_data(&bc[i + 1]);
                // CREATE AND REPLACE THE BYTECODE
            }
        } 
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
        let builder = FunctionDataBuilder::new(&func_env, data.clone());

        // let x: $T = begin_forall_lambda<$T>();
        // let _ = $f(&x);
        // end_forall_lambda()

        // start, end, replace
        let conditions = [
            (env.prover_begin_forall_lambda_qid(), env.prover_end_forall_lambda_qid(), QuantifierType::Forall),
            (env.prover_begin_exists_lambda_qid(), env.prover_end_exists_lambda_qid(), QuantifierType::Exists),
        ];

        for condition in conditions {
            self.find_and_replace_macro(condition, code);
        }

        data
    }

    fn name(&self) -> String {
        "macro_quantifiers_analysis".to_string()
    }
}
