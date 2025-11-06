use std::{collections::BTreeMap};

use move_model::{
    model::{FunId, FunctionEnv, QualifiedId},
};

use crate::{
    function_data_builder::FunctionDataBuilder,
    function_target::{FunctionData},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation, AssignKind},
};

pub struct ReplacementAnalysisProcessor();

impl ReplacementAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    fn is_fn(code: &Bytecode, qid: QualifiedId<FunId>) -> Option<(&Vec<usize>, &Vec<usize>)> {
        match code {
            Bytecode::Call(_, dest, Operation::Function(mid, fid, _), srcs, _) =>
                if qid == mid.qualified(*fid) {
                    return Some((dest, srcs));
                }
            _ => {},
        }

        None
    }

    pub fn find_ref_val_patterns(&self, func_env: &FunctionEnv, data: &FunctionData) -> BTreeMap<usize, (Vec<usize>, Vec<usize>)> {
        let mut matches = BTreeMap::new();
        for i in 0..data.code.len() - 1 {
            if let Some((dest_val, srcs_val)) = Self::is_fn(&data.code[i], func_env.module_env.env.prover_val_qid()) {
                if let Some((dest_ref, srcs_ref)) = Self::is_fn(&data.code[i + 1], func_env.module_env.env.prover_ref_qid()) {
                    if dest_val == srcs_ref {
                        matches.insert(i, (dest_ref.clone(), srcs_val.clone()));
                    }
                }
            }
        }

        matches
    }

    pub fn replace_patterns(&self, patterns: BTreeMap<usize, (Vec<usize>, Vec<usize>)>, func_env: &FunctionEnv, data: FunctionData) -> FunctionData {
        if patterns.is_empty() {
            return data;
        }

        let mut new_data = data.clone();
        new_data.code = vec![];

        let mut builder = FunctionDataBuilder::new(func_env, new_data);
        for (offset, bc) in data.code.into_iter().enumerate() {
            if patterns.contains_key(&offset) {
                continue;
            } else if offset > 0 && patterns.contains_key(&(offset - 1)) {
                let (dest, srcs) = patterns.get(&(offset - 1)).unwrap();
                builder.emit(Bytecode::Assign(bc.get_attr_id(), dest[0], srcs[0].clone(), AssignKind::Copy));
            } else {
                builder.emit(bc);
            }
        }

        builder.data
    }
}

impl FunctionTargetProcessor for ReplacementAnalysisProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !targets.is_spec(&func_env.get_qualified_id()) {
            // only need to do this for spec functions
            return data;
        }

        let patterns = self.find_ref_val_patterns(func_env, &data);
        self.replace_patterns(patterns, func_env, data)
    }

    fn name(&self) -> String {
        "replacement_analysis".to_string()
    }
}
