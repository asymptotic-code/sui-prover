// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function body translation

use crate::control_flow_reconstruction::phi_detection::detect_phis;
use crate::control_flow_reconstruction::structure_discovery::reconstruct_function;
use crate::control_flow_reconstruction::DiscoveryContext;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::{
    Function, FunctionSignature, IRNode, Parameter, Type, VariableRegistry,
};
use move_model::model::FunctionEnv;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::graph::{DomRelation, Graph};
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};
use crate::translation::ir_translator::build_trace_map;

pub fn translate_function(builder: &mut ProgramBuilder, target: FunctionTarget) -> Function {
    let variables = VariableRegistry::new(
        builder.convert_types(&target.data.local_types)
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| (format!("$t{}", idx), ty))
            .collect()
    );

    let func_env = target.func_env;
    let module_id = builder
        .program
        .modules
        .id_for_key(func_env.module_env.get_id());

    let body = if func_env.is_native() {
        // Native functions have no body
        IRNode::default()
    } else if target.get_bytecode().is_empty() {
        // Non-native function with empty bytecode - likely inlined/optimized by compiler
        IRNode::default()
    } else {
        let forward_cfg =
            StacklessControlFlowGraph::new_forward_with_options(target.get_bytecode(), true);
        let forward_dom = build_dominator_relation(&forward_cfg);
        detect_phis(reconstruct_function(DiscoveryContext {
            trace_names: build_trace_map(&target),
            builder,
            target,
            forward_dom,
            forward_cfg
        }))
    };

    // Check if this is a spec function by detecting requires/ensures in body
    // Note: #[spec(prove)] attributes don't survive compilation to bytecode,
    // so we detect spec functions by their IR structure
    let is_spec_function = contains_spec_nodes(&body);

    Function {
        module_id,
        name: ProgramBuilder::sanitize_name(&builder.symbol_str(func_env.get_name())),
        signature: build_signature(builder, func_env),
        body,
        variables,
        mutual_group_id: None,
        is_native: func_env.is_native(),
        is_spec_function,
        is_monadic: false,  // Will be set by analyze_monadicity pass
    }
}

fn build_signature(builder: &mut ProgramBuilder, func_env: &FunctionEnv) -> FunctionSignature {
    FunctionSignature {
        type_params: builder.sanitize_type_params(&func_env.get_type_parameters()),
        parameters: func_env
            .get_parameters()
            .iter()
            .enumerate()
            .map(|(i, param)| {
                let name = builder.symbol_str(param.0).to_string();
                Parameter {
                    name: if name == "_" {
                        format!("param{}", i)
                    } else {
                        name
                    },
                    param_type: builder.convert_type(&param.1),
                    ssa_value: format!("$t{}", i),
                }
            })
            .collect(),
        return_type: {
            let types = builder.convert_types(&func_env.get_return_types());
            match types.len() {
                0 => Type::Tuple(vec![]),
                1 => types.into_iter().next().unwrap(),
                _ => Type::Tuple(types),
            }.wrap_in_monad()
        },
    }
}

fn build_dominator_relation(cfg: &StacklessControlFlowGraph) -> DomRelation<BlockId> {
    let entry = cfg.entry_block();
    let nodes = cfg.blocks();
    let edges = nodes
        .iter()
        .flat_map(|block| cfg.successors(*block).iter().map(|succ| (*block, *succ)))
        .collect::<Vec<_>>();
    DomRelation::new(&Graph::new(entry, nodes, edges))
}

/// Check if IR body contains requires or ensures nodes
fn contains_spec_nodes(body: &IRNode) -> bool {
    body.iter().any(|node| matches!(node, IRNode::Requires(_) | IRNode::Ensures(_)))
}
