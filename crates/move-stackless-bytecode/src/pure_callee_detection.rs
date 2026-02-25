// Copyright (c) Mysten Labs
// SPDX-License-Identifier: Apache-2.0

//! Identifies functions transitively called by `#[ext(pure)]` functions and
//! marks them as pure callee candidates. Validation is done later by
//! `PureFunctionAnalysisProcessor`.

use std::collections::{BTreeSet, VecDeque};

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
        // BFS from pure functions to collect all transitive callee candidates
        let mut visited = BTreeSet::new();
        let mut queue = VecDeque::new();

        for qid in targets.get_funs() {
            if targets.is_pure_fun(&qid) {
                for callee in env.get_function(qid).get_called_functions() {
                    if visited.insert(callee) {
                        queue.push_back(callee);
                    }
                }
            }
        }

        while let Some(qid) = queue.pop_front() {
            for callee in env.get_function(qid).get_called_functions() {
                if visited.insert(callee) {
                    queue.push_back(callee);
                }
            }

            // Mark non-pure, non-native, non-intrinsic functions as pure callees
            if targets.is_pure_fun(&qid) || env.should_be_used_as_func(&qid) {
                continue;
            }
            let fun_env = env.get_function(qid);
            if fun_env.is_native() || fun_env.is_intrinsic() {
                continue;
            }
            targets.add_pure_callee(qid);
        }
    }

    fn name(&self) -> String {
        "pure_callee_detection".to_string()
    }
}
