// Copyright (c) Mysten Labs
// SPDX-License-Identifier: Apache-2.0

//! Identifies functions transitively called by `#[ext(pure)]` functions and
//! validates them as pure callee candidates.
//!
//! Runs before `ConditionalMergeInsertionProcessor` so that pure callees get
//! the IfThenElse treatment needed for Boogie function emission.
//!
//! Uses `initialize()` to BFS from pure functions, then `process()` (called in
//! topological order by the pipeline) to validate each candidate.

use std::collections::{BTreeSet, VecDeque};

use move_model::model::{FunId, FunctionEnv, GlobalEnv, QualifiedId};

use crate::{
    deterministic_analysis,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    pure_function_analysis::PureFunctionAnalysisProcessor,
    stackless_bytecode::{Bytecode, Operation},
};

pub struct PureCalleeDetectionProcessor();

impl PureCalleeDetectionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    /// Check if bytecode satisfies pure requirements (no error messages, just bool).
    fn is_bytecode_pure_compatible(
        data: &FunctionData,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        native_pure: &BTreeSet<QualifiedId<FunId>>,
    ) -> bool {
        data.code.iter().all(|bc| {
            use Bytecode::*;
            match bc {
                Call(_, _, Operation::Function(mid, fid, _), _, _) => {
                    let qid = mid.qualified(*fid);
                    targets.can_be_pure_callee(&qid)
                        || env.should_be_used_as_func(&qid)
                        || native_pure.contains(&qid)
                }
                Abort(..) | VariantSwitch(..) | SaveMem(..) | Prop(..) => false,
                _ => true,
            }
        })
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

        // Pre-mark all viable candidates so process() can filter them.
        // We mark optimistically here; process() will remove invalid ones.
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
            // Mark as candidate; process() validates in topological order
            targets.add_pure_callee(qid);
        }
    }

    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        fun_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        let qid = fun_env.get_qualified_id();
        if !targets.is_pure_callee(&qid) {
            return data;
        }

        let native_pure =
            PureFunctionAnalysisProcessor::native_pure_variants(fun_env.module_env.env);

        // Validate pure requirements — remove from set if any check fails
        let valid = !fun_env
            .get_parameters()
            .iter()
            .any(|p| p.1.is_mutable_reference())
            && !data.local_types.iter().any(|ty| ty.is_mutable_reference())
            && data
                .annotations
                .get::<deterministic_analysis::DeterministicInfo>()
                .is_some_and(|info| info.is_deterministic)
            && Self::is_bytecode_pure_compatible(
                &data,
                fun_env.module_env.env,
                targets,
                &native_pure,
            );

        if !valid {
            targets.remove_pure_callee(&qid);
        }

        data
    }

    fn name(&self) -> String {
        "pure_callee_detection".to_string()
    }
}
