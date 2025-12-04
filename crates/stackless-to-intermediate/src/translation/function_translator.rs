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
            .into_iter().enumerate().collect()
    );

    let func_env = target.func_env;
    let module_id = builder
        .program
        .modules
        .id_for_key(func_env.module_env.get_id());

    let body = if target.get_bytecode().is_empty() || func_env.is_native() {
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

    // Check if this is a spec function with #[spec(prove)]
    let is_spec = has_spec_prove_attribute(&func_env);

    // Extract requires/ensures from spec function body
    let (requires, ensures) = if is_spec {
        extract_spec_conditions(&body)
    } else {
        (vec![], vec![])
    };

    Function {
        module_id,
        name: ProgramBuilder::sanitize_name(&builder.symbol_str(func_env.get_name())),
        signature: build_signature(builder, func_env),
        body,
        variables,
        mutual_group_id: None,
        is_native: func_env.is_native(),
        is_spec,
        requires,
        ensures,
        spec_for: None, // Will be populated later when we link spec to impl
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

/// Check if a function has the #[spec(prove)] attribute
fn has_spec_prove_attribute(func_env: &FunctionEnv) -> bool {
    use move_model::ast::Attribute;

    func_env.get_attributes().iter().any(|attr| {
        if let Attribute::Apply(_, name, sub_attrs) = attr {
            let name_str = name.display(func_env.symbol_pool()).to_string();
            if name_str == "spec" {
                return sub_attrs.iter().any(|sub_attr| {
                    if let Attribute::Apply(_, value_name, _) = sub_attr {
                        value_name.display(func_env.symbol_pool()).to_string() == "prove"
                    } else {
                        false
                    }
                });
            }
        }
        false
    })
}

/// Extract requires and ensures conditions from a spec function body
/// Removes them from the body and collects them separately
fn extract_spec_conditions(body: &IRNode) -> (Vec<IRNode>, Vec<IRNode>) {
    let mut requires = vec![];
    let mut ensures = vec![];

    // Walk through all nodes and collect requires/ensures
    for node in body.iter() {
        match node {
            IRNode::Requires(cond) => requires.push((**cond).clone()),
            IRNode::Ensures(cond) => ensures.push((**cond).clone()),
            _ => {}
        }
    }

    (requires, ensures)
}
