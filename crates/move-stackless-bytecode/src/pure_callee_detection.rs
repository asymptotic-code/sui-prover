// Copyright (c) Mysten Labs
// SPDX-License-Identifier: Apache-2.0

//! Identifies functions that are transitively called by `#[ext(pure)]` functions
//! and validates them as pure callee candidates. Only functions that satisfy pure
//! requirements are marked.
//!
//! This processor runs before `ConditionalMergeInsertionProcessor` so that
//! pure callees get the IfThenElse treatment needed for Boogie function emission.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use move_model::model::{FunId, GlobalEnv, QualifiedId};

use crate::{
    deterministic_analysis,
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder, FunctionVariant},
    pure_function_analysis::PureFunctionAnalysisProcessor,
    stackless_bytecode::{Bytecode, Operation},
};

pub struct PureCalleeDetectionProcessor();

impl PureCalleeDetectionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self())
    }

    /// Check if a function's bytecode satisfies pure requirements.
    /// Returns true if the function can be used as a pure callee.
    fn check_bytecode(
        data: &FunctionData,
        env: &GlobalEnv,
        targets: &FunctionTargetsHolder,
        native_pure: &BTreeSet<QualifiedId<FunId>>,
    ) -> bool {
        for bc in data.code.iter() {
            use Bytecode::*;
            match bc {
                Assign(_, _, _, _)
                | Load(_, _, _)
                | Ret(_, _)
                | Nop(_)
                | Jump(_, _)
                | Branch(_, _, _, _)
                | Label(_, _) => {}
                Call(_, _, op, _, _) => match op {
                    Operation::Function(mid, fid, _) => {
                        let qid = mid.qualified(*fid);
                        if !targets.can_be_pure_callee(&qid)
                            && !env.should_be_used_as_func(&qid)
                            && !native_pure.contains(&qid)
                        {
                            return false;
                        }
                    }
                    _ => {}
                },
                Abort(_, _) | VariantSwitch(_, _, _) | SaveMem(_, _, _) | Prop(_, _, _) => {
                    return false;
                }
            }
        }
        true
    }
}

impl FunctionTargetProcessor for PureCalleeDetectionProcessor {
    fn is_single_run(&self) -> bool {
        true
    }

    fn run(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {
        let native_pure = PureFunctionAnalysisProcessor::native_pure_variants(env);

        // Collect all functions transitively called by pure functions
        let mut candidates = BTreeSet::new();
        let mut queue = VecDeque::new();

        for qid in targets.get_funs() {
            if !targets.is_pure_fun(&qid) {
                continue;
            }
            let fun_env = env.get_function(qid);
            for callee_id in fun_env.get_called_functions() {
                if !candidates.contains(&callee_id) {
                    candidates.insert(callee_id);
                    queue.push_back(callee_id);
                }
            }
        }

        // BFS to collect transitive callees
        while let Some(qid) = queue.pop_front() {
            let fun_env = env.get_function(qid);
            for callee_id in fun_env.get_called_functions() {
                if !candidates.contains(&callee_id) {
                    candidates.insert(callee_id);
                    queue.push_back(callee_id);
                }
            }
        }

        // Filter to only non-pure, non-native, non-intrinsic candidates
        let candidates: BTreeSet<_> = candidates
            .into_iter()
            .filter(|qid| {
                if targets.is_pure_fun(qid)
                    || native_pure.contains(qid)
                    || env.should_be_used_as_func(qid)
                {
                    return false;
                }
                let fun_env = env.get_function(*qid);
                if fun_env.is_native() || fun_env.is_intrinsic() {
                    return false;
                }
                true
            })
            .collect();

        // Build a simple call graph among candidates for topological ordering
        // We need to process callees before callers so that can_be_pure_callee
        // returns the correct result when checking bytecode
        let topo_order = Self::topological_sort(&candidates, env);

        // Validate each candidate in topological order (callees first)
        for qid in topo_order {
            let fun_env = env.get_function(qid);

            // Check: no mutable reference parameters
            if fun_env
                .get_parameters()
                .iter()
                .any(|p| p.1.is_mutable_reference())
            {
                continue;
            }

            // Check: has baseline data
            let Some(data) = targets.get_data(&qid, &FunctionVariant::Baseline) else {
                continue;
            };

            // Check: no mutable reference locals (conditional merge requirement)
            if data.local_types.iter().any(|ty| ty.is_mutable_reference()) {
                continue;
            }

            // Check: deterministic
            if let Some(det_info) = data
                .annotations
                .get::<deterministic_analysis::DeterministicInfo>()
            {
                if !det_info.is_deterministic {
                    continue;
                }
            } else {
                continue;
            }

            // Check: bytecode is pure-compatible
            if !Self::check_bytecode(data, env, targets, &native_pure) {
                continue;
            }

            targets.add_pure_callee(qid);
        }
    }

    fn name(&self) -> String {
        "pure_callee_detection".to_string()
    }
}

impl PureCalleeDetectionProcessor {
    /// Returns candidates in topological order: callees before callers.
    fn topological_sort(
        candidates: &BTreeSet<QualifiedId<FunId>>,
        env: &GlobalEnv,
    ) -> Vec<QualifiedId<FunId>> {
        // Build reverse adjacency (callee -> callers) and in-degree = number of
        // candidate callees. Nodes with in-degree 0 call no other candidates,
        // so they are leaf callees and should be processed first.
        let mut reverse_adj: BTreeMap<QualifiedId<FunId>, Vec<QualifiedId<FunId>>> =
            BTreeMap::new();
        let mut in_degree: BTreeMap<QualifiedId<FunId>, usize> = BTreeMap::new();

        for qid in candidates {
            reverse_adj.entry(*qid).or_default();
            in_degree.entry(*qid).or_insert(0);
            let fun_env = env.get_function(*qid);
            for callee_id in fun_env.get_called_functions() {
                if candidates.contains(&callee_id) && callee_id != *qid {
                    // Edge: callee_id -> qid (callee points to caller)
                    reverse_adj.entry(callee_id).or_default().push(*qid);
                    *in_degree.entry(*qid).or_insert(0) += 1;
                }
            }
        }

        // Kahn's algorithm: start with nodes that have no candidate callees
        let mut queue: VecDeque<_> = in_degree
            .iter()
            .filter(|(_, &deg)| deg == 0)
            .map(|(qid, _)| *qid)
            .collect();
        let mut result = Vec::new();

        while let Some(qid) = queue.pop_front() {
            result.push(qid);
            if let Some(callers) = reverse_adj.get(&qid) {
                for caller in callers {
                    let deg = in_degree.get_mut(caller).unwrap();
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(*caller);
                    }
                }
            }
        }

        // Any remaining nodes (in cycles) are skipped
        result
    }
}
