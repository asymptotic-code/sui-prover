// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Structure Discovery Phase - Builds Statement IR with expression-based control flow
//!
//! Discovers control flow structure (if/else/while) from CFG and builds Statement IR.
//! Control flow is represented as expressions (IfExpr, WhileExpr) bound via Let statements.
//! This eliminates the need for separate phi/loop variable tracking.

use super::helpers::*;
use super::DiscoveryContext;
use crate::translation::statement_translator;
use intermediate_theorem_format::{Block, Expression, LoopState, Statement, TempId, TheoremType, VariableRegistry};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};
use std::collections::{BTreeMap, BTreeSet, HashSet};

/// Maximum recursion depth before panic (indicates infinite recursion bug)
const MAX_RECURSION_DEPTH: usize = 200;

/// Result of discovering a region - includes both the statement and what it defines
struct DiscoveryResult {
    statement: Statement,
    /// Variables defined/updated in this region (name -> temp after this region)
    final_defs: BTreeMap<String, TempId>,
    /// Substitutions created by this region (old_temp -> phi_result)
    substitutions: BTreeMap<TempId, TempId>,
}

impl DiscoveryResult {
    fn empty() -> Self {
        Self {
            statement: Statement::default(),
            final_defs: BTreeMap::new(),
            substitutions: BTreeMap::new(),
        }
    }

    fn with_defs(statement: Statement, defs: BTreeMap<String, TempId>) -> Self {
        Self { statement, final_defs: defs, substitutions: BTreeMap::new() }
    }

    fn with_defs_and_subs(statement: Statement, defs: BTreeMap<String, TempId>, subs: BTreeMap<TempId, TempId>) -> Self {
        Self { statement, final_defs: defs, substitutions: subs }
    }
}

/// State passed through the recursive discovery process
struct DiscoveryState {
    /// Current recursion depth
    depth: usize,
    /// Tracks (start, stop) pairs currently being processed to detect cycles
    call_stack: HashSet<(BlockId, BlockId)>,
    /// Current variable definitions (name -> temp ID) - flowing into current region
    current_defs: BTreeMap<String, TempId>,
    /// Substitutions to apply: old_temp -> new_temp (phi results)
    substitutions: BTreeMap<TempId, TempId>,
}

impl DiscoveryState {
    fn new() -> Self {
        Self {
            depth: 0,
            call_stack: HashSet::new(),
            current_defs: BTreeMap::new(),
            substitutions: BTreeMap::new(),
        }
    }

    /// Enter a recursive call, returns false if cycle detected
    fn enter(&mut self, start: BlockId, stop: BlockId) -> bool {
        self.depth += 1;
        if self.depth > MAX_RECURSION_DEPTH {
            panic!(
                "Recursion depth exceeded {}: start={}, stop={} - this indicates infinite recursion",
                MAX_RECURSION_DEPTH, start, stop
            );
        }
        self.call_stack.insert((start, stop))
    }

    /// Exit a recursive call
    fn exit(&mut self, start: BlockId, stop: BlockId) {
        self.depth -= 1;
        self.call_stack.remove(&(start, stop));
    }

    /// Create a fresh copy of defs for a branch/loop body
    fn fork_defs(&self) -> BTreeMap<String, TempId> {
        self.current_defs.clone()
    }

    /// Record a substitution: whenever `old_temp` appears, replace with `new_temp`
    fn add_substitution(&mut self, old_temp: TempId, new_temp: TempId) {
        self.substitutions.insert(old_temp, new_temp);
    }

    /// Apply all recorded substitutions to a statement
    fn apply_substitutions(&self, stmt: Statement) -> Statement {
        if self.substitutions.is_empty() {
            return stmt;
        }
        let subs = &self.substitutions;
        stmt.map_expressions(|expr| expr.substitute_temps(subs))
    }
}

/// Information about a branch instruction
#[derive(Clone)]
struct BranchInfo {
    then_label: Label,
    else_label: Label,
    cond_temp: TempId,
    header: Statement,
    start: BlockId,
    stop: BlockId,
    incoming_defs: BTreeMap<String, TempId>,
}

/// Find immediate post-dominator of a block
fn find_immediate_post_dominator(ctx: &DiscoveryContext, block: BlockId) -> Option<BlockId> {
    StacklessControlFlowGraph::find_immediate_post_dominator(&ctx.back_cfg, block)
}

/// Collect definitions from a statement, returning the updated defs map
fn collect_defs_from_statement(
    stmt: &Statement,
    registry: &VariableRegistry,
    current_defs: &mut BTreeMap<String, TempId>,
) {
    match stmt {
        Statement::Let { results, operation, .. } => {
            for temp in results {
                if let Some(name) = registry.canonical_name(*temp) {
                    current_defs.insert(name.to_string(), *temp);
                }
            }
            // Also collect from nested IfExpr/WhileExpr if present
            collect_defs_from_expression(operation, registry, current_defs);
        }
        Statement::Sequence(stmts) => {
            for s in stmts {
                collect_defs_from_statement(s, registry, current_defs);
            }
        }
        _ => {}
    }
}

/// Collect defs from expressions (for nested control flow)
fn collect_defs_from_expression(
    expr: &Expression,
    registry: &VariableRegistry,
    current_defs: &mut BTreeMap<String, TempId>,
) {
    match expr {
        Expression::IfExpr { then_block, else_block, .. } => {
            for s in &then_block.statements {
                collect_defs_from_statement(s, registry, current_defs);
            }
            for s in &else_block.statements {
                collect_defs_from_statement(s, registry, current_defs);
            }
        }
        Expression::WhileExpr { condition, body, .. } => {
            for s in &condition.statements {
                collect_defs_from_statement(s, registry, current_defs);
            }
            for s in &body.statements {
                collect_defs_from_statement(s, registry, current_defs);
            }
        }
        _ => {}
    }
}

/// Main entry point: discover control flow structure and build Statement IR
pub fn discover_structure(ctx: &mut DiscoveryContext, start: BlockId, stop: BlockId) -> Statement {
    let mut state = DiscoveryState::new();
    let result = discover_structure_impl(ctx, start, stop, &mut state);
    result.statement
}

/// Recursive implementation of structure discovery
fn discover_structure_impl(
    ctx: &mut DiscoveryContext,
    start: BlockId,
    stop: BlockId,
    state: &mut DiscoveryState,
) -> DiscoveryResult {
    // Base case: empty region
    if start == stop {
        return DiscoveryResult::with_defs(Statement::default(), state.current_defs.clone());
    }

    // Cycle detection
    if !state.enter(start, stop) {
        // Already processing this region - break cycle
        return DiscoveryResult::with_defs(Statement::default(), state.current_defs.clone());
    }

    let result = discover_region(ctx, start, stop, state);

    state.exit(start, stop);
    result
}

/// Discover structure within a region [start, stop)
fn discover_region(
    ctx: &mut DiscoveryContext,
    start: BlockId,
    stop: BlockId,
    state: &mut DiscoveryState,
) -> DiscoveryResult {
    let mut statement = Statement::default();
    let mut cursor = start;

    while cursor != stop {
        let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, cursor) else {
            // Block has no bounds (entry/exit block), move to successor
            cursor = *ctx.forward_cfg.successors(cursor).first().unwrap_or(&stop);
            continue;
        };

        // Check for branch instruction
        if let Bytecode::Branch(_, tlabel, elabel, cond_temp) = &ctx.code[upper as usize] {
            let header = statement_translator::translate_range(ctx, lower..=upper);
            // Apply substitutions (phi results) to the header
            let header = state.apply_substitutions(header);
            collect_defs_from_statement(&header, ctx.registry, &mut state.current_defs);

            let branch_info = BranchInfo {
                then_label: *tlabel,
                else_label: *elabel,
                cond_temp: *cond_temp as TempId,
                header: header.clone(),
                start,
                stop,
                incoming_defs: state.current_defs.clone(),
            };

            let branch_result = handle_branch(ctx, &mut cursor, &branch_info, state);

            // Update current_defs from the branch result
            state.current_defs = branch_result.final_defs.clone();

            // Merge substitutions from the branch result
            for (old_temp, new_temp) in branch_result.substitutions {
                state.substitutions.insert(old_temp, new_temp);
            }

            // For While loops, DON'T prepend the header - the condition computation
            // is already inside the loop's condition block
            let is_while = matches!(&branch_result.statement, Statement::Let { operation: Expression::WhileExpr { .. }, .. });
            let combined = if is_while {
                branch_result.statement
            } else {
                header.combine(branch_result.statement)
            };

            // Check if this is a loop that consumed the entire region
            let is_loop_from_start = is_while && {
                let then_block = resolve_label_block(ctx, branch_info.then_label).unwrap();
                let else_block = resolve_label_block(ctx, branch_info.else_label).unwrap();
                then_block == start || else_block == start
            };

            statement = if is_loop_from_start {
                combined // Loop from start replaces accumulated statements
            } else {
                statement.combine(combined)
            };
            continue;
        }

        // Non-branch block: translate and move to successor
        cursor = *ctx.forward_cfg.successors(cursor).first().unwrap_or(&stop);
        let block_stmt = statement_translator::translate_range(ctx, lower..=upper);
        // Apply substitutions (phi results) to this statement
        let block_stmt = state.apply_substitutions(block_stmt);
        collect_defs_from_statement(&block_stmt, ctx.registry, &mut state.current_defs);
        statement = statement.combine(block_stmt);
    }

    DiscoveryResult::with_defs(statement, state.current_defs.clone())
}

/// Handle branch instruction - build IfExpr or WhileExpr wrapped in Let
fn handle_branch(
    ctx: &mut DiscoveryContext,
    cursor: &mut BlockId,
    branch_info: &BranchInfo,
    state: &mut DiscoveryState,
) -> DiscoveryResult {
    let then_block = resolve_label_block(ctx, branch_info.then_label)
        .expect("Branch then label must resolve to a valid block");
    let else_block = resolve_label_block(ctx, branch_info.else_label)
        .expect("Branch else label must resolve to a valid block");

    // Detect back edges (loops)
    let then_jumps_back = is_back_edge(ctx, *cursor, then_block, branch_info.start);
    let else_jumps_back = is_back_edge(ctx, *cursor, else_block, branch_info.start);

    if then_jumps_back || else_jumps_back {
        return build_while_loop(ctx, cursor, branch_info, state, then_block, else_block, then_jumps_back);
    }

    // If statement - find merge point
    let merge_block = find_immediate_post_dominator(ctx, *cursor).unwrap_or(branch_info.stop);

    // Check for degenerate loop case
    if (then_block == branch_info.start || else_block == branch_info.start)
        && merge_block == branch_info.stop
    {
        let then_is_back = then_block == branch_info.start;
        return build_while_loop(
            ctx,
            cursor,
            branch_info,
            state,
            then_block,
            else_block,
            then_is_back,
        );
    }

    *cursor = merge_block;

    // Recurse into branches with fresh defs
    let mut then_defs = branch_info.incoming_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut then_defs);
    let then_result = discover_structure_impl(ctx, then_block, merge_block, state);
    let then_final_defs = state.current_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut then_defs);

    let mut else_defs = branch_info.incoming_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut else_defs);
    let else_result = discover_structure_impl(ctx, else_block, merge_block, state);
    let else_final_defs = state.current_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut else_defs);

    // Special case: unwrap loop from IF if one branch is empty and other is a loop
    if merge_block == else_block && is_essentially_while(&then_result.statement) {
        return then_result;
    }
    if merge_block == then_block && is_essentially_while(&else_result.statement) {
        return else_result;
    }

    // Build the if-expression
    build_if_expr(
        ctx,
        branch_info,
        then_result.statement,
        else_result.statement,
        &branch_info.incoming_defs,
        &then_final_defs,
        &else_final_defs,
        state,
    )
}

/// Build an if-expression wrapped in a Let statement
fn build_if_expr(
    ctx: &mut DiscoveryContext,
    branch_info: &BranchInfo,
    then_stmt: Statement,
    else_stmt: Statement,
    incoming_defs: &BTreeMap<String, TempId>,
    then_final_defs: &BTreeMap<String, TempId>,
    else_final_defs: &BTreeMap<String, TempId>,
    state: &DiscoveryState,
) -> DiscoveryResult {
    let then_terminates = then_stmt.terminates();
    let else_terminates = else_stmt.terminates();

    // Apply substitution to condition temp if needed
    let cond_temp = state.substitutions.get(&branch_info.cond_temp)
        .copied()
        .unwrap_or(branch_info.cond_temp);

    // If both branches terminate, no values need to be merged
    if then_terminates && else_terminates {
        // Just return the if as a statement (both branches return/abort)
        let then_block = Block::new(flatten_to_stmts(then_stmt), Expression::Tuple(vec![]));
        let else_block = Block::new(flatten_to_stmts(else_stmt), Expression::Tuple(vec![]));

        let if_expr = Expression::IfExpr {
            condition: Box::new(Expression::Temporary(cond_temp)),
            then_block,
            else_block,
        };

        // No results since both branches terminate
        let stmt = Statement::Let {
            results: vec![],
            operation: if_expr,
            result_types: vec![],
        };

        return DiscoveryResult::with_defs(stmt, incoming_defs.clone());
    }

    // Find variables that need to be merged (assigned in at least one branch)
    let mut merge_vars: BTreeSet<String> = BTreeSet::new();

    // Collect all variables assigned in either branch
    for name in then_final_defs.keys().chain(else_final_defs.keys()) {
        let then_temp = then_final_defs.get(name);
        let else_temp = else_final_defs.get(name);
        let incoming_temp = incoming_defs.get(name);

        // Need merge if assigned in at least one branch and differs from incoming
        let then_changed = then_temp.map(|t| Some(t) != incoming_temp).unwrap_or(false);
        let else_changed = else_temp.map(|t| Some(t) != incoming_temp).unwrap_or(false);

        if then_changed || else_changed {
            merge_vars.insert(name.clone());
        }
    }

    // If no variables need merging, just emit a side-effect if
    if merge_vars.is_empty() {
        let then_block = Block::new(flatten_to_stmts(then_stmt), Expression::Tuple(vec![]));
        let else_block = Block::new(flatten_to_stmts(else_stmt), Expression::Tuple(vec![]));

        let if_expr = Expression::IfExpr {
            condition: Box::new(Expression::Temporary(branch_info.cond_temp)),
            then_block,
            else_block,
        };

        let stmt = Statement::Let {
            results: vec![],
            operation: if_expr,
            result_types: vec![],
        };

        return DiscoveryResult::with_defs(stmt, incoming_defs.clone());
    }

    // Build result temps and expressions for each branch
    let merge_names: Vec<String> = merge_vars.into_iter().collect();
    let mut result_temps = Vec::new();
    let mut result_types = Vec::new();
    let mut then_results = Vec::new();
    let mut else_results = Vec::new();
    let mut final_defs = incoming_defs.clone();
    let mut substitutions: BTreeMap<TempId, TempId> = BTreeMap::new();

    for name in &merge_names {
        // Get the temp from each branch (or incoming if not assigned in that branch)
        let then_temp = then_final_defs.get(name)
            .or_else(|| incoming_defs.get(name))
            .copied();
        let else_temp = else_final_defs.get(name)
            .or_else(|| incoming_defs.get(name))
            .copied();

        // Skip if we can't find valid temps for both branches
        // (This shouldn't happen if tracking is correct, but let's be safe)
        let (then_val, else_val) = match (then_temp, else_temp, then_terminates, else_terminates) {
            // Normal case: both branches have values
            (Some(t), Some(e), false, false) => (t, e),
            // Then branch terminates: use else value for both (then value is unreachable)
            (_, Some(e), true, false) => (e, e),
            // Else branch terminates: use then value for both (else value is unreachable)
            (Some(t), _, false, true) => (t, t),
            // Both terminate: skip this variable (values are unreachable)
            (_, _, true, true) => continue,
            // Missing temp: skip this merge (shouldn't happen with correct tracking)
            _ => continue,
        };

        // Get type from one of the temps
        let ty = ctx.registry.get_type(then_val)
            .or_else(|| ctx.registry.get_type(else_val))
            .cloned()
            .unwrap_or(TheoremType::Bool); // Fallback (shouldn't happen)

        // Allocate a new temp for the merge result
        let result_temp = ctx.registry.alloc_local(format!("phi_{}", name), ty.clone());

        result_temps.push(result_temp);
        result_types.push(ty);
        then_results.push(Expression::Temporary(then_val));
        else_results.push(Expression::Temporary(else_val));

        // Update final defs to point to the merge result
        final_defs.insert(name.clone(), result_temp);

        // Record substitutions: original temps should be replaced with phi result
        // Both then_val and else_val should map to result_temp for subsequent code
        if then_val != result_temp {
            substitutions.insert(then_val, result_temp);
        }
        if else_val != result_temp && else_val != then_val {
            substitutions.insert(else_val, result_temp);
        }
    }

    // Build blocks with result expressions
    let then_result_expr = if then_results.len() == 1 {
        then_results.pop().unwrap()
    } else {
        Expression::Tuple(then_results)
    };
    let else_result_expr = if else_results.len() == 1 {
        else_results.pop().unwrap()
    } else {
        Expression::Tuple(else_results)
    };

    let then_block = Block::new(flatten_to_stmts(then_stmt), then_result_expr);
    let else_block = Block::new(flatten_to_stmts(else_stmt), else_result_expr);

    let if_expr = Expression::IfExpr {
        condition: Box::new(Expression::Temporary(cond_temp)),
        then_block,
        else_block,
    };

    let stmt = Statement::Let {
        results: result_temps,
        operation: if_expr,
        result_types,
    };

    DiscoveryResult::with_defs_and_subs(stmt, final_defs, substitutions)
}

/// Check if jumping to target from current block is a back edge
fn is_back_edge(ctx: &DiscoveryContext, current: BlockId, target: BlockId, region_start: BlockId) -> bool {
    target == current
        || ctx.forward_dom.is_dominated_by(current, target)
        || target == region_start
}

/// Build a while loop as WhileExpr wrapped in Let
fn build_while_loop(
    ctx: &mut DiscoveryContext,
    cursor: &mut BlockId,
    branch_info: &BranchInfo,
    state: &mut DiscoveryState,
    then_block_id: BlockId,
    else_block_id: BlockId,
    then_is_body: bool,
) -> DiscoveryResult {
    let (loop_body_start, loop_exit) = if then_is_body {
        (then_block_id, else_block_id)
    } else {
        (else_block_id, then_block_id)
    };
    let loop_header = *cursor;
    *cursor = loop_exit;

    // Discover loop body with fresh defs
    let mut loop_defs = state.fork_defs();
    std::mem::swap(&mut state.current_defs, &mut loop_defs);
    let body_result = discover_structure_impl(ctx, loop_body_start, loop_header, state);
    let body_final_defs = state.current_defs.clone();
    std::mem::swap(&mut state.current_defs, &mut loop_defs);

    // Extract condition computation
    let condition_stmt = extract_condition_dependencies(
        &branch_info.header,
        branch_info.cond_temp,
        ctx.registry,
    );

    // Find loop-carried variables: assigned in body and used before assignment
    let mut loop_vars: Vec<(String, TempId, TempId)> = Vec::new(); // (name, initial, updated)

    for (name, updated_temp) in &body_final_defs {
        if let Some(initial_temp) = branch_info.incoming_defs.get(name) {
            // Variable was defined before loop and updated in body
            if initial_temp != updated_temp {
                loop_vars.push((name.clone(), *initial_temp, *updated_temp));
            }
        }
    }

    // If no loop variables, emit a simple while (rare but possible for side-effect-only loops)
    if loop_vars.is_empty() {
        let condition_block = Block::new(
            flatten_to_stmts(condition_stmt),
            Expression::Temporary(branch_info.cond_temp),
        );
        let body_block = Block::new(
            flatten_to_stmts(body_result.statement),
            Expression::Tuple(vec![]),
        );

        let while_expr = Expression::WhileExpr {
            condition: condition_block,
            body: body_block,
            state: LoopState {
                vars: vec![],
                types: vec![],
                initial: vec![],
            },
        };

        let stmt = Statement::Let {
            results: vec![],
            operation: while_expr,
            result_types: vec![],
        };

        return DiscoveryResult::with_defs(stmt, branch_info.incoming_defs.clone());
    }

    // Build loop state
    let mut state_vars = Vec::new();
    let mut state_types = Vec::new();
    let mut initial_exprs = Vec::new();
    let mut result_temps = Vec::new();
    let mut updated_exprs = Vec::new();
    let mut final_defs = branch_info.incoming_defs.clone();

    for (name, initial_temp, updated_temp) in &loop_vars {
        let ty = ctx.registry.get_type(*initial_temp)
            .or_else(|| ctx.registry.get_type(*updated_temp))
            .cloned()
            .unwrap_or(TheoremType::Bool); // Fallback (shouldn't happen)

        // Allocate a state variable for the loop
        let state_var = ctx.registry.alloc_local(format!("loop_{}", name), ty.clone());

        state_vars.push(state_var);
        state_types.push(ty.clone());
        initial_exprs.push(Expression::Temporary(*initial_temp));
        updated_exprs.push(Expression::Temporary(*updated_temp));

        // Allocate result temp for after the loop
        let result_temp = ctx.registry.alloc_local(format!("loop_result_{}", name), ty);
        result_temps.push(result_temp);

        final_defs.insert(name.clone(), result_temp);
    }

    // Build condition block - needs to use loop state vars
    let condition_block = Block::new(
        flatten_to_stmts(condition_stmt),
        Expression::Temporary(branch_info.cond_temp),
    );

    // Build body block - result is the updated state
    let body_result_expr = if updated_exprs.len() == 1 {
        updated_exprs.pop().unwrap()
    } else {
        Expression::Tuple(updated_exprs)
    };
    let body_block = Block::new(
        flatten_to_stmts(body_result.statement),
        body_result_expr,
    );

    let while_expr = Expression::WhileExpr {
        condition: condition_block,
        body: body_block,
        state: LoopState {
            vars: state_vars,
            types: state_types.clone(),
            initial: initial_exprs,
        },
    };

    let stmt = Statement::Let {
        results: result_temps,
        operation: while_expr,
        result_types: state_types,
    };

    DiscoveryResult::with_defs(stmt, final_defs)
}

/// Extract only the statements from `header` that are needed to compute `cond_temp`.
fn extract_condition_dependencies(
    header: &Statement,
    cond_temp: TempId,
    registry: &VariableRegistry,
) -> Statement {
    let stmts = flatten_to_stmts(header.clone());
    if stmts.is_empty() {
        return Statement::default();
    }

    // Build a map from temp -> statement index that defines it
    let mut def_map: BTreeMap<TempId, usize> = BTreeMap::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        for temp in get_defined_temps(stmt) {
            def_map.insert(temp, idx);
        }
    }

    // Backward pass: find all statements needed to compute cond_temp
    let mut needed: BTreeSet<usize> = BTreeSet::new();
    let mut worklist: Vec<TempId> = vec![cond_temp];

    while let Some(temp) = worklist.pop() {
        if let Some(&idx) = def_map.get(&temp) {
            if needed.insert(idx) {
                for used_temp in get_used_temps(&stmts[idx], registry) {
                    worklist.push(used_temp);
                }
            }
        }
    }

    // Collect needed statements in original order
    let result_stmts: Vec<Statement> = stmts
        .into_iter()
        .enumerate()
        .filter(|(idx, _)| needed.contains(idx))
        .map(|(_, stmt)| stmt)
        .collect();

    match result_stmts.len() {
        0 => Statement::default(),
        1 => result_stmts.into_iter().next().unwrap(),
        _ => Statement::Sequence(result_stmts),
    }
}

/// Flatten a statement into a vector of statements
fn flatten_to_stmts(stmt: Statement) -> Vec<Statement> {
    match stmt {
        Statement::Sequence(stmts) => stmts.into_iter().flat_map(flatten_to_stmts).collect(),
        s if matches!(s, Statement::Sequence(ref v) if v.is_empty()) => vec![],
        s => vec![s],
    }
}

/// Get the temp IDs defined by a statement
fn get_defined_temps(stmt: &Statement) -> Vec<TempId> {
    match stmt {
        Statement::Let { results, .. } => results.clone(),
        _ => vec![],
    }
}

/// Get the temp IDs used by a statement's expressions
fn get_used_temps(stmt: &Statement, registry: &VariableRegistry) -> Vec<TempId> {
    let mut temps = Vec::new();
    for expr in stmt.iter_expressions() {
        temps.extend(expr.iter_temps());
    }
    temps.into_iter().filter(|t| registry.get_name(*t).is_some()).collect()
}

/// Check if a statement is essentially a while loop
fn is_essentially_while(stmt: &Statement) -> bool {
    match stmt {
        Statement::Let { operation: Expression::WhileExpr { .. }, .. } => true,
        Statement::Sequence(stmts) => stmts.last().map(is_essentially_while).unwrap_or(false),
        _ => false,
    }
}

