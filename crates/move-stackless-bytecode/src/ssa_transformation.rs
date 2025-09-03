// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use move_binary_format::file_format::CodeOffset;
use move_model::model::FunctionEnv;

use crate::{
    ast::TempIndex,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::Bytecode,
    stackless_control_flow_graph::StacklessControlFlowGraph,
};

pub struct SSATransformProcessor {
    debug: bool,
}

impl SSATransformProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self { debug: false })
    }

    pub fn new_with_debug() -> Box<Self> {
        Box::new(Self { debug: true })
    }

    fn collect_conditionals(
        &self,
        target: &FunctionTarget<'_>,
        cfg: &StacklessControlFlowGraph,
    ) -> Vec<ConditionalPattern> {
        let mut conditionals = Vec::new();
        let code = &target.data.code;

        for (pc, bytecode) in code.iter().enumerate() {
            if let Bytecode::Branch(_attr_id, true_label, false_label, condition) = bytecode {
                if self.debug {
                    println!("  Found branch at PC {} with condition {:?}", pc, condition);
                }

                let cond = ConditionalPattern {
                    condition: *condition,
                    branch_pc: pc as CodeOffset,
                    true_branch: BTreeMap::new(),
                    false_branch: BTreeMap::new(),
                    phi_vars: BTreeSet::new(),
                    merge_pc: pc as CodeOffset + 1,
                };

                conditionals.push(cond);
            }
        }

        if self.debug {
            println!("Found {} conditionals", conditionals.len());
        }

        conditionals
    }
}

/// Conditional expression state
#[derive(Debug, Clone)]
struct ConditionalPattern {
    condition: TempIndex,
    branch_pc: CodeOffset,
    /// Represents block of assignments: temp_var -> value
    true_branch: BTreeMap<TempIndex, TempIndex>,
    false_branch: BTreeMap<TempIndex, TempIndex>,
    /// Phi nodes for variables at merge point
    phi_vars: BTreeSet<TempIndex>,
    merge_pc: CodeOffset,
}

impl FunctionTargetProcessor for SSATransformProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        if self.debug {
            println!(
                "Processing function {} for SSA transformation",
                func_env.get_full_name_str()
            );
        }

        let target = FunctionTarget::new(func_env, &data);
        let cfg = StacklessControlFlowGraph::new_forward(&data.code);
        let _conditionals = self.collect_conditionals(&target, &cfg);

        if self.debug {
            println!(
                "SSA transformation completed for {}",
                func_env.get_full_name_str()
            );
        }

        data
    }

    fn name(&self) -> String {
        "ssa_transform".to_owned()
    }
}
