// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function body translation

use crate::control_flow_reconstruction::structure_discovery::reconstruct_function;
use crate::control_flow_reconstruction::DiscoveryContext;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::{FunctionSignature, IRNode, Parameter, TheoremFunction, TheoremType, VariableRegistry};
use move_model::model::FunctionEnv;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::graph::{DomRelation, Graph};
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};

pub fn translate_function(
    builder: &mut ProgramBuilder,
    target: FunctionTarget,
) -> TheoremFunction {
    let mut variables = VariableRegistry::new(target.data.local_types.iter().enumerate()
        .map(|(index, move_type)| (index, builder.convert_type(move_type)))
        .collect());
    
    let func_env = target.func_env;
    let module_id = builder.program.modules.id_for_key(func_env.module_env.get_id());
    let name = ProgramBuilder::sanitize_name(&builder.symbol_str(func_env.get_name()));
    let signature = build_signature(builder, func_env);
    let is_native = func_env.is_native();
    
    if target.get_bytecode().is_empty() || is_native {
        return TheoremFunction {
            module_id,
            name,
            signature,
            body: IRNode::default(),
            variables,
            mutual_group_id: None,
            is_native,
        };
    }
    
    let forward_cfg = StacklessControlFlowGraph::new_forward_with_options(target.get_bytecode(), true);
    let forward_dom = build_dominator_relation(&forward_cfg);
    let ctx = DiscoveryContext { builder, target, variables: &mut variables, forward_dom, forward_cfg };
    let body = reconstruct_function(ctx);
    
    TheoremFunction {
        module_id,
        name,
        signature,
        body,
        variables,
        mutual_group_id: None,
        is_native,
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
            let types: Vec<_> = func_env
                .get_return_types()
                .iter()
                .map(|t| builder.convert_type(t))
                .collect();
            match types.len() {
                0 => TheoremType::Tuple(vec![]),
                1 => types.into_iter().next().unwrap(),
                _ => TheoremType::Tuple(types),
            }
                .wrap_in_monad()
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