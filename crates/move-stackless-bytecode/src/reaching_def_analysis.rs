// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Reaching definition analysis with subsequent copy propagation.
//
// This analysis and transformation only propagates definitions, leaving dead assignments
// in the code. The subsequent livevar_analysis takes care of removing those.

use std::collections::{BTreeMap, BTreeSet};

use itertools::Itertools;

use move_binary_format::file_format::CodeOffset;
use move_model::model::FunctionEnv;

use crate::{
    ast::TempIndex,
    dataflow_analysis::{DataflowAnalysis, TransferFunctions},
    dataflow_domains::{AbstractDomain, JoinResult},
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{BorrowNode, Bytecode, Operation},
    stackless_control_flow_graph::StacklessControlFlowGraph,
};

// The map stores transitive alias chains: x -> {y, z} means x = y and y = z
type DefMap = BTreeMap<TempIndex, BTreeSet<TempIndex>>;

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Default)]
pub struct ReachingDefState {
    pub map: DefMap,
}

/// The annotation for reaching definitions. For each code position, we have a map of local
/// indices to the set of definitions reaching the code position.
#[derive(Default)]
pub struct ReachingDefAnnotation(BTreeMap<CodeOffset, ReachingDefState>);

pub struct ReachingDefProcessor {}

impl ReachingDefProcessor {
    pub fn new() -> Box<Self> {
        Box::new(ReachingDefProcessor {})
    }

    /// Gets the propagated local resolving aliases using the reaching definitions.
    /// For x -> {y, z, ...}, pick one that maps to empty set (is a root).
    /// If multiple roots, pick the one with lowest temp index.
    fn get_propagated_local(temp: TempIndex, state: &ReachingDefState) -> TempIndex {
        state
            .map
            .get(&temp)
            .and_then(|aliases| {
                aliases
                    .iter()
                    .filter(|a| !state.map.contains_key(a))
                    .min()
                    .copied()
            })
            .unwrap_or(temp)
    }

    /// Perform copy propagation based on reaching definitions analysis results.
    pub fn copy_propagation(
        target: &FunctionTarget<'_>,
        code: Vec<Bytecode>,
        defs: &ReachingDefAnnotation,
    ) -> Vec<Bytecode> {
        let default_state = ReachingDefState::default();

        let mut res = vec![];
        for (pc, bytecode) in code.into_iter().enumerate() {
            let state = defs.0.get(&(pc as CodeOffset)).unwrap_or(&default_state);
            let mut propagate = |local| Self::get_propagated_local(local, state);
            res.push(bytecode.remap_src_vars(target.global_env(), &mut propagate));
        }
        res
    }

    /// Compute the set of locals which are borrowed from or which are otherwise used to refer to.
    /// We can't alias such locals to other locals because of reference semantics.
    fn borrowed_locals(code: &[Bytecode]) -> BTreeSet<TempIndex> {
        use Bytecode::*;
        code.iter()
            .filter_map(|bc| match bc {
                Call(_, _, Operation::BorrowLoc, srcs, _) => Some(srcs[0]),
                Call(_, _, Operation::WriteBack(BorrowNode::LocalRoot(src), ..), ..)
                | Call(_, _, Operation::IsParent(BorrowNode::LocalRoot(src), ..), ..) => Some(*src),
                Call(_, _, Operation::WriteBack(BorrowNode::Reference(src), ..), ..)
                | Call(_, _, Operation::IsParent(BorrowNode::Reference(src), ..), ..) => Some(*src),
                _ => None,
            })
            .collect()
    }

    /// Performs reaching definition analysis and returns the state per instruction.
    pub fn analyze_reaching_definitions(
        func_env: &FunctionEnv,
        data: &FunctionData,
    ) -> BTreeMap<CodeOffset, ReachingDefState> {
        let cfg = StacklessControlFlowGraph::new_forward(&data.code);
        let analyzer = ReachingDefAnalysis {
            _target: FunctionTarget::new(func_env, &data),
            borrowed_locals: Self::borrowed_locals(&data.code),
        };
        let block_state_map = analyzer.analyze_function(
            ReachingDefState {
                map: BTreeMap::new(),
            },
            &data.code,
            &cfg,
        );
        analyzer.state_per_instruction(block_state_map, &data.code, &cfg, |before, _| {
            before.clone()
        })
    }

    pub fn all_aliases(state: &ReachingDefState, temp_idx: &TempIndex) -> BTreeSet<TempIndex> {
        state.map.get(temp_idx).cloned().unwrap_or_default()
    }
}

impl FunctionTargetProcessor for ReachingDefProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if !func_env.is_native() {
            let per_bytecode_state = Self::analyze_reaching_definitions(func_env, &data);

            // Run copy propagation transformation.
            let annotations = ReachingDefAnnotation(per_bytecode_state);
            let code = std::mem::take(&mut data.code);
            let target = FunctionTarget::new(func_env, &data);
            let new_code = Self::copy_propagation(&target, code, &annotations);
            data.code = new_code;

            // Currently we do not need reaching defs after this phase. If so in the future, we
            // need to uncomment this statement.
            //data.annotations.set(annotations);
        }

        data
    }

    fn name(&self) -> String {
        "reaching_def_analysis".to_string()
    }
}

struct ReachingDefAnalysis<'a> {
    _target: FunctionTarget<'a>,
    borrowed_locals: BTreeSet<TempIndex>,
}

impl ReachingDefAnalysis<'_> {}

impl TransferFunctions for ReachingDefAnalysis<'_> {
    type State = ReachingDefState;
    const BACKWARD: bool = false;

    fn execute(&self, state: &mut ReachingDefState, instr: &Bytecode, _offset: CodeOffset) {
        use Bytecode::*;

        for dest in instr.dests() {
            state.kill(dest);
        }

        match instr {
            Assign(_, dest, src, _) => {
                if !self.borrowed_locals.contains(dest) && !self.borrowed_locals.contains(src) {
                    state.def_alias(*dest, *src);
                }
            }
            Call(_, _, Operation::WriteBack(BorrowNode::LocalRoot(local), ..), _, _) => {
                state.kill(*local);
            }
            _ => {}
        }
    }
}

impl DataflowAnalysis for ReachingDefAnalysis<'_> {}

impl AbstractDomain for ReachingDefState {
    fn join(&mut self, other: &Self) -> JoinResult {
        let mut result = JoinResult::Unchanged;
        // intersection: only keep keys that exist in both, with intersected values
        for idx in self.map.keys().cloned().collect_vec() {
            if let Some(other_aliases) = other.map.get(&idx) {
                let self_aliases = self.map.get_mut(&idx).unwrap();
                let intersection: BTreeSet<TempIndex> =
                    self_aliases.intersection(other_aliases).copied().collect();
                if intersection != *self_aliases {
                    if intersection.is_empty() {
                        self.map.remove(&idx);
                    } else {
                        *self_aliases = intersection;
                    }
                    result = JoinResult::Changed;
                }
            } else {
                self.map.remove(&idx);
                result = JoinResult::Changed;
            }
        }

        result
    }
}

impl ReachingDefState {
    // def_alias(dest, src): insert dest -> {src} union map[src]
    fn def_alias(&mut self, dest: TempIndex, src: TempIndex) {
        let mut aliases = BTreeSet::new();
        aliases.insert(src);
        if let Some(src_aliases) = self.map.get(&src) {
            aliases.extend(src_aliases.iter().copied());
        }
        self.map.insert(dest, aliases);
    }

    // kill(dest): remove entry for dest and remove dest from all entries
    fn kill(&mut self, dest: TempIndex) {
        self.map.remove(&dest);
        self.map.retain(|_, aliases| {
            aliases.remove(&dest);
            !aliases.is_empty()
        });
    }
}

// =================================================================================================
// Formatting

/// Format a reaching definition annotation.
pub fn format_reaching_def_annotation(
    target: &FunctionTarget<'_>,
    code_offset: CodeOffset,
) -> Option<String> {
    if let Some(ReachingDefAnnotation(map)) =
        target.get_annotations().get::<ReachingDefAnnotation>()
    {
        if let Some(map_at) = map.get(&code_offset) {
            let mut res = map_at
                .map
                .iter()
                .map(|(idx, aliases)| {
                    let name = target.get_local_name(*idx);
                    format!(
                        "{} -> {{{}}}",
                        name.display(target.symbol_pool()),
                        aliases
                            .iter()
                            .map(|a| {
                                format!(
                                    "{}",
                                    target.get_local_name(*a).display(target.symbol_pool())
                                )
                            })
                            .join(", ")
                    )
                })
                .join(", ");
            res.insert_str(0, "reach: ");
            return Some(res);
        }
    }
    None
}
