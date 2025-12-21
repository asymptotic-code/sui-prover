// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Function body translation

use crate::control_flow_reconstruction::phi_detection::detect_phis;
use crate::control_flow_reconstruction::structure_discovery::reconstruct_function;
use crate::control_flow_reconstruction::DiscoveryContext;
use crate::program_builder::ProgramBuilder;
use intermediate_theorem_format::{
    Function, FunctionFlags, FunctionID, FunctionSignature, IRNode, Parameter, Type,
    VariableRegistry,
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

    let (body, has_early_return_in_while) = if func_env.is_native() {
        // Native functions have no body
        (IRNode::default(), false)
    } else if target.get_bytecode().is_empty() {
        // Non-native function with empty bytecode - likely inlined/optimized by compiler
        (IRNode::default(), false)
    } else {
        let forward_cfg =
            StacklessControlFlowGraph::new_forward_with_options(target.get_bytecode(), true);
        let forward_dom = build_dominator_relation(&forward_cfg);
        let raw_body = reconstruct_function(DiscoveryContext {
            trace_names: build_trace_map(&target),
            builder,
            target,
            forward_dom,
            forward_cfg
        });
        // Check for early return in while loops BEFORE phi detection transforms the IR
        let has_early_return_in_while = raw_body.has_early_return_in_while();
        // Collect BOTH SSA names ($t0, $t1, etc.) AND human-readable parameter names (low, high, etc.)
        // This ensures parameters can be detected as loop-modified variables regardless of which name is used
        let param_count = func_env.get_parameter_count();
        let mut param_names: Vec<String> = (0..param_count).map(|i| format!("$t{}", i)).collect();
        // Also add human-readable names from parameters
        for (i, param) in func_env.get_parameters().iter().enumerate() {
            let name = builder.symbol_str(param.0).to_string();
            if name != "_" && name != format!("$t{}", i) {
                param_names.push(name);
            }
        }
        (detect_phis(raw_body, param_names), has_early_return_in_while)
    };

    // Check if this is a spec function by detecting requires/ensures in body
    // Note: #[spec(prove)] attributes don't survive compilation to bytecode,
    // so we detect spec functions by their IR structure
    let func_name = ProgramBuilder::sanitize_name(&builder.symbol_str(func_env.get_name()));
    let is_spec = contains_spec_nodes(
        &func_name,
        &body,
        builder.invariant_begin_id,
        builder.invariant_end_id,
    );

    let mut flags = FunctionFlags::new();
    // Mark as native if: truly native OR has early return in while loop (can't be translated)
    flags.set_native(func_env.is_native() || has_early_return_in_while);
    flags.set_spec(is_spec);

    Function {
        module_id,
        name: ProgramBuilder::sanitize_name(&builder.symbol_str(func_env.get_name())),
        signature: build_signature(builder, func_env),
        body,
        variables,
        mutual_group_id: None,
        flags,
        spec_target: None, // Set later via set_spec_targets if this is a spec function
        original_body: None, // Set later if body is replaced by spec
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

/// Check if IR body contains TOP-LEVEL requires or ensures nodes (spec function markers).
/// Loop invariants don't count - they're inside While nodes or invariant_begin/end blocks.
fn contains_spec_nodes(
    func_name: &str,
    body: &IRNode,
    invariant_begin_id: Option<FunctionID>,
    invariant_end_id: Option<FunctionID>,
) -> bool {
    // Only check direct children, not nodes inside While loops or invariant blocks
    fn check_node(
        func_name: &str,
        node: &IRNode,
        in_invariant: bool,
        invariant_begin_id: Option<FunctionID>,
        invariant_end_id: Option<FunctionID>,
        depth: usize,
        path: &str,
    ) -> bool {
        let new_path = format!("{}/{}", path, match node {
            IRNode::Block { .. } => "Block".to_string(),
            IRNode::If { .. } => "If".to_string(),
            IRNode::Let { pattern, .. } => format!("Let({:?})", pattern),
            IRNode::While { .. } => "While".to_string(),
            IRNode::WhileAborts { .. } => "WhileAborts".to_string(),
            IRNode::Requires(_) => "Requires".to_string(),
            IRNode::Ensures(_) => "Ensures".to_string(),
            other => format!("{:?}", std::mem::discriminant(other)),
        });
        match node {
            IRNode::Requires(_) if !in_invariant => {
                eprintln!("SPEC: {} found Requires at {}", func_name, new_path);
                true
            }
            IRNode::Ensures(_) if !in_invariant => {
                eprintln!("SPEC: {} found Ensures at {}", func_name, new_path);
                true
            }
            IRNode::Requires(_) | IRNode::Ensures(_) => {
                // Inside invariant block - skip
                false
            }
            IRNode::Block { children } => {
                // Track invariant_begin/invariant_end to skip ensures inside invariant blocks
                let mut in_inv = in_invariant;
                for child in children {
                    // Check for invariant_begin call
                    if is_call_to(child, invariant_begin_id) {
                        in_inv = true;
                    } else if is_call_to(child, invariant_end_id) {
                        in_inv = false;
                    } else if check_node(func_name, child, in_inv, invariant_begin_id, invariant_end_id, depth + 1, &new_path) {
                        return true;
                    }
                }
                false
            }
            IRNode::If { cond, then_branch, else_branch } => {
                check_node(func_name, cond, in_invariant, invariant_begin_id, invariant_end_id, depth + 1, &format!("{}/cond", new_path)) ||
                check_node(func_name, then_branch, in_invariant, invariant_begin_id, invariant_end_id, depth + 1, &format!("{}/then", new_path)) ||
                check_node(func_name, else_branch, in_invariant, invariant_begin_id, invariant_end_id, depth + 1, &format!("{}/else", new_path))
            }
            IRNode::Let { pattern: _, value, .. } => {
                check_node(func_name, value, in_invariant, invariant_begin_id, invariant_end_id, depth + 1, &new_path)
            }
            // Don't recurse into While - invariants inside loops don't mark spec functions
            IRNode::While { .. } | IRNode::WhileAborts { .. } => false,
            _ => false,
        }
    }
    let result = check_node(func_name, body, false, invariant_begin_id, invariant_end_id, 0, "");
    if result {
        eprintln!("SPEC: {} -> is_spec=true", func_name);
    }
    result
}

/// Check if a node is a call to a specific function (wrapped in Let { value: Call { ... } })
fn is_call_to(node: &IRNode, target_id: Option<FunctionID>) -> bool {
    let target = match target_id {
        Some(id) => id,
        None => return false,
    };

    if let IRNode::Let { value, .. } = node {
        if let IRNode::Call { function, .. } = value.as_ref() {
            // Compare base IDs (ignore variant)
            return function.base == target.base;
        }
    }
    false
}
