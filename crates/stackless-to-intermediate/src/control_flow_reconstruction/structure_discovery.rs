// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Structure Discovery - Builds IR with expression-based control flow

use super::helpers::{block_bounds, resolve_label_block};
use super::DiscoveryContext;
use crate::translation::ir_translator;
use intermediate_theorem_format::{IRNode, VariableRegistry};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::BlockId;
use std::collections::{BTreeMap, BTreeSet, HashSet};

struct DiscoveryResult {
    nodes: Vec<IRNode>,
    final_defs: BTreeSet<String>,
    substitutions: BTreeMap<String, String>,
}

impl DiscoveryResult {
    fn with_defs(nodes: Vec<IRNode>, defs: BTreeSet<String>) -> Self {
        Self { nodes, final_defs: defs, substitutions: BTreeMap::new() }
    }
}

struct DiscoveryState {
    call_stack: HashSet<(BlockId, BlockId)>,
    current_defs: BTreeSet<String>,
    substitutions: BTreeMap<String, String>,
}

impl DiscoveryState {
    fn new() -> Self {
        Self { call_stack: HashSet::new(), current_defs: BTreeSet::new(), substitutions: BTreeMap::new() }
    }

    fn enter(&mut self, start: BlockId, stop: BlockId) -> bool {
        self.call_stack.insert((start, stop))
    }

    fn exit(&mut self, start: BlockId, stop: BlockId) {
        self.call_stack.remove(&(start, stop));
    }

    fn fork_defs(&self) -> BTreeSet<String> {
        self.current_defs.clone()
    }

    fn apply_substitutions(&self, ir: IRNode) -> IRNode {
        if self.substitutions.is_empty() { ir } else { ir.substitute_vars(&self.substitutions) }
    }
}

#[derive(Clone)]
struct BranchInfo {
    then_label: Label,
    else_label: Label,
    cond_name: String,
    header: Vec<IRNode>,
    start: BlockId,
    stop: BlockId,
    pre_header_defs: BTreeSet<String>,
    incoming_defs: BTreeSet<String>,
}

pub fn reconstruct_function(mut ctx: DiscoveryContext) -> IRNode {
    let mut state = DiscoveryState::new();
    let entry = ctx.forward_cfg.entry_block();
    let exit = ctx.forward_cfg.exit_block();
    let result = discover_structure(&mut ctx, entry, exit, &mut state);
    IRNode::Block { children: result.nodes }
}

fn discover_structure(
    ctx: &mut DiscoveryContext,
    start: BlockId,
    stop: BlockId,
    state: &mut DiscoveryState,
) -> DiscoveryResult {
    if start == stop {
        return DiscoveryResult::with_defs(vec![], state.current_defs.clone());
    }

    if !state.enter(start, stop) {
        return DiscoveryResult::with_defs(vec![], state.current_defs.clone());
    }

    let result = discover_region(ctx, start, stop, state);
    state.exit(start, stop);
    result
}

fn discover_region(
    ctx: &mut DiscoveryContext,
    start: BlockId,
    stop: BlockId,
    state: &mut DiscoveryState,
) -> DiscoveryResult {
    let mut nodes: Vec<IRNode> = vec![];
    let mut cursor = start;

    while cursor != stop {
        let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, cursor) else {
            cursor = *ctx.forward_cfg.successors(cursor).first().unwrap_or(&stop);
            continue;
        };

        if let Bytecode::Branch(_, tlabel, elabel, cond_temp) = ctx.target.get_bytecode()[upper as usize].clone() {
            let then_label = tlabel;
            let else_label = elabel;
            let cond_name = ir_translator::temp_id(&ctx.target, cond_temp);

            let pre_header_defs = state.current_defs.clone();
            let header_nodes: Vec<IRNode> = ir_translator::translate_range(ctx, lower..=upper)
                .into_iter()
                .map(|ir| state.apply_substitutions(ir))
                .collect();
            collect_defs_from_ir_list(&header_nodes, &mut state.current_defs);

            let branch_info = BranchInfo {
                then_label,
                else_label,
                cond_name,
                header: header_nodes.clone(),
                start,
                stop,
                pre_header_defs,
                incoming_defs: state.current_defs.clone(),
            };

            let branch_result = handle_branch(ctx, &mut cursor, &branch_info, state);
            state.current_defs = branch_result.final_defs.clone();
            state.substitutions.extend(branch_result.substitutions);

            let is_while = branch_result.nodes.last()
                .map(|ir| matches!(ir, IRNode::Let { value, .. } if matches!(value.as_ref(), IRNode::While { .. })))
                .unwrap_or(false);

            let is_loop_from_start = is_while && {
                let then_block = resolve_label_block(ctx, branch_info.then_label).unwrap();
                let else_block = resolve_label_block(ctx, branch_info.else_label).unwrap();
                then_block == start || else_block == start
            };

            if is_loop_from_start {
                nodes = branch_result.nodes;
            } else if is_while {
                nodes.extend(branch_result.nodes);
            } else {
                nodes.extend(header_nodes);
                nodes.extend(branch_result.nodes);
            }
            continue;
        }

        cursor = *ctx.forward_cfg.successors(cursor).first().unwrap_or(&stop);
        for ir in ir_translator::translate_range(ctx, lower..=upper) {
            let ir = state.apply_substitutions(ir);
            collect_defs_from_ir(&ir, &mut state.current_defs);
            nodes.push(ir);
        }
    }

    DiscoveryResult::with_defs(nodes, state.current_defs.clone())
}

fn handle_branch(
    ctx: &mut DiscoveryContext,
    cursor: &mut BlockId,
    branch_info: &BranchInfo,
    state: &mut DiscoveryState,
) -> DiscoveryResult {
    let then_block = resolve_label_block(ctx, branch_info.then_label).expect("then label must resolve");
    let else_block = resolve_label_block(ctx, branch_info.else_label).expect("else label must resolve");

    let then_jumps_back = is_back_edge(ctx, *cursor, then_block, branch_info.start);
    let else_jumps_back = is_back_edge(ctx, *cursor, else_block, branch_info.start);

    if then_jumps_back || else_jumps_back {
        return build_while_loop(ctx, cursor, branch_info, state, then_block, else_block, then_jumps_back);
    }

    let merge_block = find_merge_block(&ctx.forward_cfg, then_block, else_block, branch_info.stop)
        .unwrap_or(branch_info.stop);

    if (then_block == branch_info.start || else_block == branch_info.start) && merge_block == branch_info.stop {
        return build_while_loop(ctx, cursor, branch_info, state, then_block, else_block, then_block == branch_info.start);
    }

    *cursor = merge_block;

    let mut then_defs = branch_info.incoming_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut then_defs);
    let then_result = discover_structure(ctx, then_block, merge_block, state);
    std::mem::swap(&mut state.current_defs, &mut then_defs);

    let mut else_defs = branch_info.incoming_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut else_defs);
    let else_result = discover_structure(ctx, else_block, merge_block, state);
    std::mem::swap(&mut state.current_defs, &mut else_defs);

    if merge_block == else_block && is_essentially_while(&then_result.nodes) {
        return then_result;
    }
    if merge_block == then_block && is_essentially_while(&else_result.nodes) {
        return else_result;
    }

    build_if_expr(branch_info, then_result.nodes, else_result.nodes, &branch_info.incoming_defs, state)
}

fn build_if_expr(
    branch_info: &BranchInfo,
    then_nodes: Vec<IRNode>,
    else_nodes: Vec<IRNode>,
    incoming_defs: &BTreeSet<String>,
    state: &DiscoveryState,
) -> DiscoveryResult {
    let cond_name = state.substitutions.get(&branch_info.cond_name).cloned().unwrap_or_else(|| branch_info.cond_name.clone());
    let cond_expr = IRNode::Var(cond_name);

    let then_terminates = then_nodes.iter().any(|ir| ir.terminates());
    let else_terminates = else_nodes.iter().any(|ir| ir.terminates());

    if then_terminates && else_terminates {
        let stmt = build_side_effect_if(cond_expr, then_nodes, else_nodes);
        return DiscoveryResult::with_defs(vec![stmt], incoming_defs.clone());
    }

    let then_assignments = collect_direct_assignments(&then_nodes);
    let else_assignments = collect_direct_assignments(&else_nodes);
    let merge_vars = find_merge_variables(&then_assignments, &else_assignments, incoming_defs, then_terminates, else_terminates);

    if merge_vars.is_empty() {
        let stmt = build_side_effect_if(cond_expr, then_nodes, else_nodes);
        return DiscoveryResult::with_defs(vec![stmt], incoming_defs.clone());
    }

    let merge_names: Vec<String> = merge_vars.into_iter().collect();
    let mut final_defs = incoming_defs.clone();
    for name in &merge_names {
        final_defs.insert(name.clone());
    }

    // If one branch terminates, keep it as-is and only extract values from the other
    if then_terminates {
        // then branch aborts, else branch produces the values
        let (else_nodes_filtered, else_final_values) = extract_final_assignments(&else_nodes, &merge_names);
        let mut else_results = Vec::new();
        for name in &merge_names {
            let value = else_final_values.get(name).cloned()
                .or_else(|| incoming_defs.contains(name).then(|| IRNode::Var(name.clone())))
                .unwrap_or_else(|| panic!("BUG: Variable '{}' must be defined in else branch", name));
            else_results.push(value);
        }
        let mut else_children = else_nodes_filtered;
        else_children.push(results_to_expr(else_results));

        let if_expr = IRNode::If {
            cond: Box::new(cond_expr),
            then_branch: Box::new(IRNode::Block { children: then_nodes }),
            else_branch: Box::new(IRNode::Block { children: else_children }),
        };
        let stmt = IRNode::Let { pattern: merge_names, value: Box::new(if_expr) };
        return DiscoveryResult::with_defs(vec![stmt], final_defs);
    }

    if else_terminates {
        // else branch aborts, then branch produces the values
        let (then_nodes_filtered, then_final_values) = extract_final_assignments(&then_nodes, &merge_names);
        let mut then_results = Vec::new();
        for name in &merge_names {
            let value = then_final_values.get(name).cloned()
                .or_else(|| incoming_defs.contains(name).then(|| IRNode::Var(name.clone())))
                .unwrap_or_else(|| panic!("BUG: Variable '{}' must be defined in then branch", name));
            then_results.push(value);
        }
        let mut then_children = then_nodes_filtered;
        then_children.push(results_to_expr(then_results));

        let if_expr = IRNode::If {
            cond: Box::new(cond_expr),
            then_branch: Box::new(IRNode::Block { children: then_children }),
            else_branch: Box::new(IRNode::Block { children: else_nodes }),
        };
        let stmt = IRNode::Let { pattern: merge_names, value: Box::new(if_expr) };
        return DiscoveryResult::with_defs(vec![stmt], final_defs);
    }

    // Normal case: neither terminates, both produce values
    let (then_nodes_filtered, then_final_values) = extract_final_assignments(&then_nodes, &merge_names);
    let (else_nodes_filtered, else_final_values) = extract_final_assignments(&else_nodes, &merge_names);

    let mut then_results = Vec::new();
    let mut else_results = Vec::new();

    for name in &merge_names {
        let then_value = then_final_values.get(name).cloned()
            .or_else(|| incoming_defs.contains(name).then(|| IRNode::Var(name.clone())))
            .unwrap_or_else(|| panic!("BUG: Variable '{}' must be defined", name));
        let else_value = else_final_values.get(name).cloned()
            .or_else(|| incoming_defs.contains(name).then(|| IRNode::Var(name.clone())))
            .unwrap_or_else(|| panic!("BUG: Variable '{}' must be defined", name));

        then_results.push(then_value);
        else_results.push(else_value);
    }

    let mut then_children = then_nodes_filtered;
    then_children.push(results_to_expr(then_results));
    let mut else_children = else_nodes_filtered;
    else_children.push(results_to_expr(else_results));

    let if_expr = IRNode::If {
        cond: Box::new(cond_expr),
        then_branch: Box::new(IRNode::Block { children: then_children }),
        else_branch: Box::new(IRNode::Block { children: else_children }),
    };

    let stmt = IRNode::Let { pattern: merge_names, value: Box::new(if_expr) };
    DiscoveryResult::with_defs(vec![stmt], final_defs)
}

fn build_while_loop(
    ctx: &mut DiscoveryContext,
    cursor: &mut BlockId,
    branch_info: &BranchInfo,
    state: &mut DiscoveryState,
    then_block_id: BlockId,
    else_block_id: BlockId,
    then_is_body: bool,
) -> DiscoveryResult {
    let (loop_body_start, loop_exit) = if then_is_body { (then_block_id, else_block_id) } else { (else_block_id, then_block_id) };
    let loop_header = *cursor;
    *cursor = loop_exit;

    let mut loop_defs = state.fork_defs();
    std::mem::swap(&mut state.current_defs, &mut loop_defs);
    let body_result = discover_structure(ctx, loop_body_start, loop_header, state);
    std::mem::swap(&mut state.current_defs, &mut loop_defs);

    let condition_nodes = extract_condition_dependencies(&branch_info.header, &branch_info.cond_name);
    let body_assignments = collect_direct_assignments(&body_result.nodes);

    let loop_var_names: Vec<String> = body_assignments.keys()
        .filter(|name| {
            branch_info.pre_header_defs.contains(*name) && !VariableRegistry::is_temp(name)
        })
        .cloned()
        .collect();

    let mut cond_children = condition_nodes;
    cond_children.push(IRNode::Var(branch_info.cond_name.clone()));
    let condition_block = IRNode::Block { children: cond_children };

    if loop_var_names.is_empty() {
        let while_expr = IRNode::While {
            cond: Box::new(condition_block),
            body: Box::new(IRNode::Block { children: body_result.nodes }),
        };
        let stmt = IRNode::Let { pattern: vec![], value: Box::new(while_expr) };
        return DiscoveryResult::with_defs(vec![stmt], branch_info.incoming_defs.clone());
    }

    let mut final_defs = branch_info.incoming_defs.clone();
    let (state_var_names, updated_exprs): (Vec<_>, Vec<_>) = loop_var_names.iter()
        .map(|name| {
            final_defs.insert(name.clone());
            (name.clone(), IRNode::Var(name.clone()))
        })
        .unzip();

    let mut body_children = body_result.nodes;
    body_children.push(results_to_expr(updated_exprs));

    let while_expr = IRNode::While {
        cond: Box::new(condition_block),
        body: Box::new(IRNode::Block { children: body_children }),
    };

    let stmt = IRNode::Let { pattern: state_var_names, value: Box::new(while_expr) };
    DiscoveryResult::with_defs(vec![stmt], final_defs)
}

fn build_side_effect_if(cond_expr: IRNode, then_nodes: Vec<IRNode>, else_nodes: Vec<IRNode>) -> IRNode {
    IRNode::Let {
        pattern: vec![],
        value: Box::new(IRNode::If {
            cond: Box::new(cond_expr),
            then_branch: Box::new(IRNode::Block { children: then_nodes }),
            else_branch: Box::new(IRNode::Block { children: else_nodes }),
        }),
    }
}

fn is_back_edge(ctx: &DiscoveryContext, current: BlockId, target: BlockId, region_start: BlockId) -> bool {
    target == current || ctx.forward_dom.is_dominated_by(current, target) || target == region_start
}

fn is_essentially_while(nodes: &[IRNode]) -> bool {
    nodes.last().map(|ir| matches!(ir, IRNode::Let { value, .. } if matches!(value.as_ref(), IRNode::While { .. }))).unwrap_or(false)
}

fn results_to_expr(mut results: Vec<IRNode>) -> IRNode {
    if results.len() == 1 { results.pop().unwrap() } else { IRNode::Tuple(results) }
}

fn collect_defs_from_ir(ir: &IRNode, current_defs: &mut BTreeSet<String>) {
    if let IRNode::Let { pattern, value, .. } = ir {
        for name in pattern {
            current_defs.insert(name.clone());
        }
        collect_defs_from_ir_recursive(value, current_defs);
    }
}

fn collect_defs_from_ir_list(nodes: &[IRNode], current_defs: &mut BTreeSet<String>) {
    nodes.iter().for_each(|ir| collect_defs_from_ir(ir, current_defs));
}

fn collect_defs_from_ir_recursive(ir: &IRNode, current_defs: &mut BTreeSet<String>) {
    match ir {
        IRNode::If { then_branch, else_branch, .. } => {
            collect_defs_from_block_ir(then_branch, current_defs);
            collect_defs_from_block_ir(else_branch, current_defs);
        }
        IRNode::While { cond, body, .. } => {
            collect_defs_from_block_ir(cond, current_defs);
            collect_defs_from_block_ir(body, current_defs);
        }
        IRNode::Block { children } => children.iter().for_each(|c| collect_defs_from_ir(c, current_defs)),
        _ => {}
    }
}

fn collect_defs_from_block_ir(ir: &IRNode, current_defs: &mut BTreeSet<String>) {
    match ir {
        IRNode::Block { children } => children.iter().for_each(|c| collect_defs_from_ir(c, current_defs)),
        _ => collect_defs_from_ir(ir, current_defs),
    }
}

fn collect_direct_assignments(nodes: &[IRNode]) -> BTreeMap<String, IRNode> {
    nodes.iter().filter_map(|ir| {
        if let IRNode::Let { pattern, value, .. } = ir {
            Some(pattern.iter().map(|name| (name.clone(), value.as_ref().clone())))
        } else {
            None
        }
    }).flatten().collect()
}

fn find_merge_variables(
    then_assignments: &BTreeMap<String, IRNode>,
    else_assignments: &BTreeMap<String, IRNode>,
    incoming_defs: &BTreeSet<String>,
    then_terminates: bool,
    else_terminates: bool,
) -> BTreeSet<String> {
    let mut merge_vars = BTreeSet::new();

    // If one branch terminates and the other doesn't, include:
    // 1. Variables that were already defined before the if AND updated in the non-terminating branch
    // 2. Variables named tmp#$X which are typically return-value temporaries
    if then_terminates && !else_terminates {
        for name in else_assignments.keys() {
            if incoming_defs.contains(name) || name.starts_with("tmp#") {
                merge_vars.insert(name.clone());
            }
        }
        return merge_vars;
    }
    if else_terminates && !then_terminates {
        for name in then_assignments.keys() {
            if incoming_defs.contains(name) || name.starts_with("tmp#") {
                merge_vars.insert(name.clone());
            }
        }
        return merge_vars;
    }

    // Normal case: both branches continue
    // A variable is a merge variable if:
    // 1. It's assigned in BOTH branches (value comes from whichever branch executes), OR
    // 2. It's assigned in ONE branch AND was defined before the if (so the other branch
    //    can use the incoming value)
    for name in then_assignments.keys() {
        if else_assignments.contains_key(name) {
            // Assigned in both branches - definitely a merge variable
            merge_vars.insert(name.clone());
        } else if incoming_defs.contains(name) {
            // Assigned in then only, but was defined before - merge with incoming
            merge_vars.insert(name.clone());
        }
        // If assigned in then only and NOT in incoming_defs, it's local to then branch
    }
    for name in else_assignments.keys() {
        if !then_assignments.contains_key(name) && incoming_defs.contains(name) {
            // Assigned in else only, but was defined before - merge with incoming
            merge_vars.insert(name.clone());
        }
        // Already handled: assigned in both (above), or assigned only here and not in incoming (local)
    }
    merge_vars
}

fn extract_final_assignments(
    nodes: &[IRNode],
    merge_vars: &[String],
) -> (Vec<IRNode>, BTreeMap<String, IRNode>) {
    let merge_set: BTreeSet<&String> = merge_vars.iter().collect();
    let mut final_values: BTreeMap<String, IRNode> = BTreeMap::new();
    let mut found_vars: BTreeSet<String> = BTreeSet::new();
    let mut filtered_nodes: Vec<IRNode> = Vec::new();

    for ir in nodes.iter().rev() {
        if let IRNode::Let { pattern, value, .. } = ir {
            if pattern.len() == 1 {
                let name = &pattern[0];
                if merge_set.contains(name) && !found_vars.contains(name) {
                    found_vars.insert(name.clone());
                    final_values.insert(name.clone(), value.as_ref().clone());
                    continue;
                }
            } else {
                // Multi-element pattern: check if any merge vars are in it
                // For multi-element patterns, the value for each var is just Var(name)
                // since the Let binding will destructure the value
                let mut any_extracted = false;
                for name in pattern {
                    if merge_set.contains(name) && !found_vars.contains(name) {
                        found_vars.insert(name.clone());
                        final_values.insert(name.clone(), IRNode::Var(name.clone()));
                        any_extracted = true;
                    }
                }
                // Keep the Let binding since it defines other variables too
                if any_extracted {
                    filtered_nodes.push(ir.clone());
                    continue;
                }
            }
        }
        filtered_nodes.push(ir.clone());
    }

    filtered_nodes.reverse();
    (filtered_nodes, final_values)
}

fn extract_condition_dependencies(header_nodes: &[IRNode], cond_name: &str) -> Vec<IRNode> {
    if header_nodes.is_empty() {
        return vec![];
    }

    let def_map: BTreeMap<String, usize> = header_nodes.iter().enumerate()
        .flat_map(|(idx, ir)| get_defined_names(ir).into_iter().map(move |name| (name, idx)))
        .collect();

    let mut needed: BTreeSet<usize> = BTreeSet::new();
    let mut worklist: Vec<String> = vec![cond_name.to_string()];

    while let Some(name) = worklist.pop() {
        if let Some(&idx) = def_map.get(&name) {
            if needed.insert(idx) {
                worklist.extend(header_nodes[idx].used_vars().map(|s| s.to_string()));
            }
        }
    }

    header_nodes.iter().enumerate()
        .filter(|(idx, _)| needed.contains(idx))
        .map(|(_, ir)| ir.clone())
        .collect()
}

fn get_defined_names(ir: &IRNode) -> Vec<String> {
    match ir {
        IRNode::Let { pattern, .. } => pattern.clone(),
        _ => vec![],
    }
}

fn find_merge_block(
    cfg: &move_stackless_bytecode::stackless_control_flow_graph::StacklessControlFlowGraph,
    then_block: BlockId,
    else_block: BlockId,
    stop: BlockId,
) -> Option<BlockId> {
    let mut then_reachable: BTreeSet<BlockId> = BTreeSet::new();
    let mut worklist = vec![then_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !then_reachable.insert(block) {
            continue;
        }
        worklist.extend(cfg.successors(block));
    }

    let mut else_reachable: BTreeSet<BlockId> = BTreeSet::new();
    let mut worklist = vec![else_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !else_reachable.insert(block) {
            continue;
        }
        worklist.extend(cfg.successors(block));
    }

    then_reachable.intersection(&else_reachable).copied().min()
}
