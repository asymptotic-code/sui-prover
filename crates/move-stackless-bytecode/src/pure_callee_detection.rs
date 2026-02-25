// Copyright (c) Mysten Labs
// SPDX-License-Identifier: Apache-2.0

//! Identifies functions transitively called by `#[ext(pure)]` functions and
//! marks them as pure callee candidates. Validation is done later by
//! `PureFunctionAnalysisProcessor`.

use std::collections::VecDeque;

use move_model::model::GlobalEnv;

use crate::function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder};

pub struct PureCalleeDetectionProcessor();

impl PureCalleeDetectionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }
}

impl FunctionTargetProcessor for PureCalleeDetectionProcessor {
    fn is_single_run(&self) -> bool {
        true
    }

    fn run(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        // Seed BFS with pure functions
        let mut queue: VecDeque<_> = targets
            .get_funs()
            .into_iter()
            .filter(|qid| targets.is_pure_fun(qid))
            .collect();

        while let Some(qid) = queue.pop_front() {
            for callee in env.get_function(qid).get_called_functions() {
                if targets.is_pure_callee(&callee) || targets.is_pure_fun(&callee) {
                    continue;
                }
                let fun_env = env.get_function(callee);
                if fun_env.is_native() || fun_env.is_intrinsic() {
                    continue;
                }
                targets.add_pure_callee(callee);
                queue.push_back(callee);
            }
        }
    }

    fn name(&self) -> String {
        "pure_callee_detection".to_string()
    }
}
