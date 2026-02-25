// Copyright (c) Mysten Labs
// SPDX-License-Identifier: Apache-2.0

//! Identifies functions transitively called by `#[ext(pure)]` functions and
//! marks them as pure callee candidates. Validation is done later by
//! `PureFunctionAnalysisProcessor`.

use std::collections::{BTreeSet, VecDeque};

use move_model::model::{FunctionEnv, GlobalEnv};

use crate::{
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    pure_function_analysis::PureFunctionAnalysisProcessor,
};

pub struct PureCalleeDetectionProcessor();

impl PureCalleeDetectionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for PureCalleeDetectionProcessor {
    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // BFS from pure functions to collect all transitive callee candidates
        let mut candidates = BTreeSet::new();
        let mut queue = VecDeque::new();

        for qid in targets.get_funs() {
            if targets.is_pure_fun(&qid) {
                let fun_env = env.get_function(qid);
                for callee in fun_env.get_called_functions() {
                    if candidates.insert(callee) {
                        queue.push_back(callee);
                    }
                }
            }
        }

        while let Some(qid) = queue.pop_front() {
            let fun_env = env.get_function(qid);
            for callee in fun_env.get_called_functions() {
                if candidates.insert(callee) {
                    queue.push_back(callee);
                }
            }
        }

        // Mark viable candidates (skip already-pure, native, intrinsic)
        let native_pure = PureFunctionAnalysisProcessor::native_pure_variants(env);
        for qid in candidates {
            if targets.is_pure_fun(&qid)
                || native_pure.contains(&qid)
                || env.should_be_used_as_func(&qid)
            {
                continue;
            }
            let fun_env = env.get_function(qid);
            if fun_env.is_native() || fun_env.is_intrinsic() {
                continue;
            }
            targets.add_pure_callee(qid);
        }
    }

    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        _fun_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        data
    }

    fn name(&self) -> String {
        "pure_callee_detection".to_string()
    }
}
