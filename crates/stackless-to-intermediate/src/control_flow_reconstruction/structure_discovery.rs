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
use intermediate_theorem_format::{Block, Expression, LetPattern, Statement, TempId, TheoremType, VariableRegistry};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::{BlockId, StacklessControlFlowGraph};
use std::collections::{BTreeMap, BTreeSet, HashSet};

/// Result of discovering a region - includes both the statement and what it defines
struct DiscoveryResult {
    statement: Statement,
    /// Variables defined/updated in this region (name -> temp after this region)
    final_defs: BTreeMap<String, TempId>,
    /// Substitutions created by this region (old_name -> new_name)
    substitutions: BTreeMap<String, String>,
}

impl DiscoveryResult {
    fn with_defs(statement: Statement, defs: BTreeMap<String, TempId>) -> Self {
        Self { statement, final_defs: defs, substitutions: BTreeMap::new() }
    }
}

/// State passed through the recursive discovery process
struct DiscoveryState {
    /// Tracks (start, stop) pairs currently being processed to detect cycles
    call_stack: HashSet<(BlockId, BlockId)>,
    /// Current variable definitions (name -> temp ID) - flowing into current region
    current_defs: BTreeMap<String, TempId>,
    /// Substitutions to apply: old_name -> new_name
    substitutions: BTreeMap<String, String>,
}

impl DiscoveryState {
    fn new() -> Self {
        Self {
            call_stack: HashSet::new(),
            current_defs: BTreeMap::new(),
            substitutions: BTreeMap::new(),
        }
    }

    /// Enter a recursive call, returns false if cycle detected
    fn enter(&mut self, start: BlockId, stop: BlockId) -> bool {
        self.call_stack.insert((start, stop))
    }

    /// Exit a recursive call
    fn exit(&mut self, start: BlockId, stop: BlockId) {
        self.call_stack.remove(&(start, stop));
    }

    /// Create a fresh copy of defs for a branch/loop body
    fn fork_defs(&self) -> BTreeMap<String, TempId> {
        self.current_defs.clone()
    }

    /// Apply all recorded substitutions to a statement
    fn apply_substitutions(&self, stmt: Statement) -> Statement {
        if self.substitutions.is_empty() {
            return stmt;
        }
        stmt.map_expressions(|expr| expr.substitute_vars(&self.substitutions))
    }
}

/// Information about a branch instruction
#[derive(Clone)]
struct BranchInfo {
    then_label: Label,
    else_label: Label,
    cond_temp: TempId,
    cond_name: String,
    header: Statement,
    start: BlockId,
    stop: BlockId,
    /// Definitions available BEFORE the header (for loop-carried variable detection)
    pre_header_defs: BTreeMap<String, TempId>,
    /// Definitions available AFTER the header (includes header temporaries)
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
        Statement::Let { pattern, value, .. } => {
            // Track each defined name by looking up its temp ID in the registry
            for name in pattern.names() {
                // Look up the temp ID for this name
                if let Some(temp_id) = registry.find_temp_by_name(name) {
                    current_defs.insert(name.to_string(), temp_id);
                }
                // If name not found in registry, it might be a generated name
                // In that case, keep existing mapping if we have one
            }
            // Also collect from nested IfExpr/WhileExpr if present
            collect_defs_from_expression(value, registry, current_defs);
        }
        Statement::Sequence(stmts) => {
            for s in stmts {
                collect_defs_from_statement(s, registry, current_defs);
            }
        }
        _ => {}
    }
}

/// Get the type of an expression if we can determine it
/// For complex expressions, recursively try to find a type from sub-expressions
fn get_expression_type(expr: &Expression, registry: &VariableRegistry) -> Option<TheoremType> {
    match expr {
        Expression::Var(_name) => {
            // Can't look up type by name alone - would need temp id
            None
        }
        Expression::Pack { struct_id, type_args, .. } => Some(TheoremType::Struct {
            struct_id: *struct_id,
            type_args: type_args.clone(),
        }),
        Expression::Cast { target_type, .. } => Some(target_type.clone()),
        Expression::FieldAccess { operand, .. } => {
            // Try to get type from the operand's temp
            get_expression_type(operand, registry)
        },
        Expression::Call { .. } => {
            // For calls, we can't easily know the return type without function info
            None
        },
        // For other expressions, we'd need more complex type inference
        // For now, return None and let other fallbacks handle it
        _ => None,
    }
}

/// Collect temps that are directly assigned in a statement (not recursively through nested control flow)
/// Returns a map of canonical name -> assigned expression
fn collect_direct_assignments(
    stmt: &Statement,
    _registry: &VariableRegistry,
) -> BTreeMap<String, Expression> {
    let mut assignments = BTreeMap::new();
    collect_direct_assignments_impl(stmt, &mut assignments);
    assignments
}

fn collect_direct_assignments_impl(
    stmt: &Statement,
    assignments: &mut BTreeMap<String, Expression>,
) {
    match stmt {
        Statement::Let { pattern, value, .. } => {
            match pattern {
                LetPattern::Single(name) => {
                    // Store the expression that's being assigned
                    assignments.insert(name.clone(), value.clone());
                }
                LetPattern::Tuple(names) => {
                    // For tuple unpacking, track each result
                    for name in names.iter() {
                        // For tuple unpacking, just mark it as a reference to the value
                        // We can't extract individual components without TupleAccess
                        assignments.insert(name.clone(), value.clone());
                    }
                }
            }
            // Don't recurse into nested IfExpr/WhileExpr - we want direct assignments only
        }
        Statement::Sequence(stmts) => {
            for s in stmts {
                collect_direct_assignments_impl(s, assignments);
            }
        }
        _ => {}
    }
}

/// Result of extracting final assignments
struct ExtractedAssignments {
    /// The expression that was assigned
    expr: Expression,
    /// The type of the result (if we can determine it)
    ty: Option<TheoremType>,
}

/// Check if a statement is a single-result Let that assigns to a merge variable
fn try_extract_merge_assignment(
    stmt: &Statement,
    merge_set: &BTreeSet<&String>,
    found_vars: &BTreeSet<String>,
    _registry: &VariableRegistry,
) -> Option<(String, ExtractedAssignments)> {
    let Statement::Let { pattern, value, types } = stmt else {
        return None;
    };

    let LetPattern::Single(name) = pattern else {
        return None;
    };

    if !merge_set.contains(name) || found_vars.contains(name) {
        return None;
    }

    let ty = types.first().cloned();

    Some((name.clone(), ExtractedAssignments {
        expr: value.clone(),
        ty,
    }))
}

/// Convert a vec of statements back to a single Statement
fn stmts_to_statement(stmts: Vec<Statement>) -> Statement {
    match stmts.len() {
        0 => Statement::default(),
        1 => stmts.into_iter().next().unwrap(),
        _ => Statement::Sequence(stmts),
    }
}

/// Extract final assignments to the given variables from a statement.
/// Returns (filtered_statement, final_values) where:
/// - filtered_statement has the final assignments removed
/// - final_values maps variable name to the expression and type that was assigned
fn extract_final_assignments(
    stmt: &Statement,
    merge_vars: &[String],
    registry: &VariableRegistry,
) -> (Statement, BTreeMap<String, ExtractedAssignments>) {
    let mut final_values: BTreeMap<String, ExtractedAssignments> = BTreeMap::new();
    let merge_set: BTreeSet<&String> = merge_vars.iter().collect();
    let mut found_vars: BTreeSet<String> = BTreeSet::new();
    let mut filtered_stmts: Vec<Statement> = Vec::new();

    // Process in reverse order to find the LAST assignment to each variable
    for s in flatten_to_stmts(stmt.clone()).into_iter().rev() {
        if let Some((name, extracted)) = try_extract_merge_assignment(&s, &merge_set, &found_vars, registry) {
            found_vars.insert(name.clone());
            final_values.insert(name, extracted);
        } else {
            filtered_stmts.push(s);
        }
    }

    filtered_stmts.reverse();
    (stmts_to_statement(filtered_stmts), final_values)
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
            // Save defs BEFORE processing header (for loop-carried variable detection)
            let pre_header_defs = state.current_defs.clone();

            let header = statement_translator::translate_range(ctx, lower..=upper);
            // Apply substitutions (phi results) to the header
            let header = state.apply_substitutions(header);
            collect_defs_from_statement(&header, ctx.registry, &mut state.current_defs);

            let cond_temp_id = *cond_temp as TempId;
            let cond_name = ctx.registry.get_name(cond_temp_id)
                .map(|s| s.to_string())
                .unwrap_or_else(|| format!("tmp__{}", cond_temp_id));

            let branch_info = BranchInfo {
                then_label: *tlabel,
                else_label: *elabel,
                cond_temp: cond_temp_id,
                cond_name: cond_name,
                header: header.clone(),
                start,
                stop,
                pre_header_defs,
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
            let is_while = matches!(&branch_result.statement, Statement::Let { value: Expression::WhileExpr { .. }, .. });
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

/// Build an if statement that produces no values (side-effect only or terminating)
fn build_side_effect_if(cond_expr: Expression, then_stmt: Statement, else_stmt: Statement) -> Statement {
    let then_block = Block::new(flatten_to_stmts(then_stmt), Expression::Tuple(vec![]));
    let else_block = Block::new(flatten_to_stmts(else_stmt), Expression::Tuple(vec![]));

    let if_expr = Expression::IfExpr {
        condition: Box::new(cond_expr),
        then_block,
        else_block,
    };

    Statement::Let { pattern: LetPattern::Tuple(vec![]), value: if_expr, types: vec![] }
}

/// Find variables that need to be merged at an if-else join point
fn find_merge_variables(
    then_assignments: &BTreeMap<String, Expression>,
    else_assignments: &BTreeMap<String, Expression>,
    incoming_defs: &BTreeMap<String, TempId>,
) -> BTreeSet<String> {
    let mut merge_vars = BTreeSet::new();

    // Case 1: Variable existed before if, assigned in one or both branches (reassignment)
    // Case 2: Variable defined in BOTH branches but not before (new phi node)
    for name in then_assignments.keys() {
        if incoming_defs.contains_key(name) || else_assignments.contains_key(name) {
            merge_vars.insert(name.clone());
        }
    }
    for name in else_assignments.keys() {
        if incoming_defs.contains_key(name) {
            merge_vars.insert(name.clone());
        }
    }

    merge_vars
}

/// Convert a vector of result expressions to a single expression (Tuple if multiple)
fn results_to_expr(mut results: Vec<Expression>) -> Expression {
    if results.len() == 1 {
        results.pop().unwrap()
    } else {
        Expression::Tuple(results)
    }
}

/// Get value for a merge variable from extracted assignments or fallback to incoming
fn get_merge_value(
    name: &str,
    extracted: Option<&ExtractedAssignments>,
    incoming_name: Option<&str>,
) -> Expression {
    extracted.map(|e| e.expr.clone())
        .or_else(|| incoming_name.map(|n| Expression::Var(n.to_string())))
        .unwrap_or_else(|| panic!("BUG: Variable '{}' must be defined in branch or have incoming value", name))
}

/// Get type for a merge variable from various sources
fn get_merge_type(
    name: &str,
    incoming_temp: Option<TempId>,
    then_extracted: Option<&ExtractedAssignments>,
    else_extracted: Option<&ExtractedAssignments>,
    then_value: &Expression,
    else_value: &Expression,
    registry: &VariableRegistry,
) -> TheoremType {
    incoming_temp.and_then(|t| registry.get_type(t).cloned())
        .or_else(|| then_extracted.and_then(|e| e.ty.clone()))
        .or_else(|| else_extracted.and_then(|e| e.ty.clone()))
        .or_else(|| get_expression_type(then_value, registry))
        .or_else(|| get_expression_type(else_value, registry))
        .unwrap_or_else(|| panic!(
            "BUG: No type found for merge variable '{}' in if-expression. then_value={:?}, else_value={:?}",
            name, then_value, else_value
        ))
}

/// Build an if-expression wrapped in a Let statement
fn build_if_expr(
    ctx: &mut DiscoveryContext,
    branch_info: &BranchInfo,
    then_stmt: Statement,
    else_stmt: Statement,
    incoming_defs: &BTreeMap<String, TempId>,
    _then_final_defs: &BTreeMap<String, TempId>,
    _else_final_defs: &BTreeMap<String, TempId>,
    state: &DiscoveryState,
) -> DiscoveryResult {
    // Apply substitution to condition name if needed
    let cond_name = state.substitutions.get(&branch_info.cond_name)
        .cloned()
        .unwrap_or_else(|| branch_info.cond_name.clone());

    // Use the condition variable as a reference. The header contains the Let
    // statement that defines this variable, so it will be available.
    // Later, temp_inlining will inline the condition expression if it's only used once.
    let cond_expr = Expression::Var(cond_name.clone());

    // If both branches terminate, no values need to be merged
    if then_stmt.terminates() && else_stmt.terminates() {
        let stmt = build_side_effect_if(cond_expr, then_stmt, else_stmt);
        return DiscoveryResult::with_defs(stmt, incoming_defs.clone());
    }

    // Collect direct assignments and find variables that need merging
    let then_assignments = collect_direct_assignments(&then_stmt, ctx.registry);
    let else_assignments = collect_direct_assignments(&else_stmt, ctx.registry);
    let merge_vars = find_merge_variables(&then_assignments, &else_assignments, incoming_defs);

    // If no variables need merging, just emit a side-effect if
    if merge_vars.is_empty() {
        let stmt = build_side_effect_if(cond_expr, then_stmt, else_stmt);
        return DiscoveryResult::with_defs(stmt, incoming_defs.clone());
    }

    // Extract final assignments that will become if-expression results
    let merge_names: Vec<String> = merge_vars.into_iter().collect();
    let (then_stmt_filtered, then_final_values) = extract_final_assignments(&then_stmt, &merge_names, ctx.registry);
    let (else_stmt_filtered, else_final_values) = extract_final_assignments(&else_stmt, &merge_names, ctx.registry);

    // Build merge results
    let mut result_names = Vec::new();
    let mut result_types = Vec::new();
    let mut then_results = Vec::new();
    let mut else_results = Vec::new();
    let mut final_defs = incoming_defs.clone();

    for name in &merge_names {
        let incoming_temp = incoming_defs.get(name).copied();
        let then_extracted = then_final_values.get(name);
        let else_extracted = else_final_values.get(name);

        // Get incoming name if it exists
        let incoming_name = incoming_temp.and_then(|t| ctx.registry.get_name(t));

        let then_value = get_merge_value(name, then_extracted, incoming_name.as_deref());
        let else_value = get_merge_value(name, else_extracted, incoming_name.as_deref());

        let ty = get_merge_type(
            name, incoming_temp, then_extracted, else_extracted,
            &then_value, &else_value, ctx.registry,
        );

        let result_temp = ctx.registry.alloc_local(name.clone(), ty.clone());

        result_names.push(name.clone());
        result_types.push(ty);
        then_results.push(then_value);
        else_results.push(else_value);
        final_defs.insert(name.clone(), result_temp);
    }

    // Build blocks and if expression
    let then_block = Block::new(flatten_to_stmts(then_stmt_filtered), results_to_expr(then_results));
    let else_block = Block::new(flatten_to_stmts(else_stmt_filtered), results_to_expr(else_results));

    let if_expr = Expression::IfExpr {
        condition: Box::new(cond_expr.clone()),
        then_block,
        else_block,
    };

    // Build the pattern from result names
    let pattern = if result_names.len() == 1 {
        LetPattern::Single(result_names.pop().unwrap())
    } else {
        LetPattern::Tuple(result_names)
    };

    let stmt = Statement::Let {
        pattern,
        value: if_expr,
        types: result_types,
    };

    DiscoveryResult::with_defs(stmt, final_defs)
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

    // Discover loop body
    let mut loop_defs = state.fork_defs();
    std::mem::swap(&mut state.current_defs, &mut loop_defs);
    let body_result = discover_structure_impl(ctx, loop_body_start, loop_header, state);
    std::mem::swap(&mut state.current_defs, &mut loop_defs);

    // Extract condition computation
    let condition_stmt = extract_condition_dependencies(
        &branch_info.header,
        &branch_info.cond_name,
        ctx.registry,
    );

    // Find loop-carried variables by looking at what the body assigns.
    // A variable is loop-carried if:
    // 1. It was defined BEFORE the loop header (not a temporary from condition computation)
    // 2. It is assigned in the body (modified by the loop)
    //
    // We use pre_header_defs (not incoming_defs) to exclude temporaries created
    // during condition evaluation. Only "real" mutable variables that existed
    // before entering the loop should be loop-carried.
    //
    // This ensures:
    // - Variables modified in the loop have their final value available after the loop
    // - The initial value (from before the loop) is passed in as loop state
    // - Each iteration can access the previous iteration's value for that variable
    // - Temporaries from condition computation are NOT included
    let body_assignments = collect_direct_assignments(&body_result.statement, ctx.registry);

    // Identify loop variables: variables that exist BEFORE the header AND are assigned in body
    // Filter out SSA temporaries (names like "t82", "t83") - we only want user-defined variables
    let loop_var_names: Vec<String> = body_assignments.keys()
        .filter(|name| {
            branch_info.pre_header_defs.contains_key(*name)
                && !is_ssa_temporary(name)
        })
        .cloned()
        .collect();

    // Build condition block
    let condition_block = Block::new(
        flatten_to_stmts(condition_stmt),
        Expression::Var(branch_info.cond_name.clone()),
    );

    // If no loop variables, emit a simple while (rare but possible for side-effect-only loops)
    if loop_var_names.is_empty() {
        let body_block = Block::new(flatten_to_stmts(body_result.statement), Expression::Tuple(vec![]));
        let while_expr = Expression::WhileExpr {
            condition: condition_block,
            body: body_block,
        };
        let stmt = Statement::Let { pattern: LetPattern::Tuple(vec![]), value: while_expr, types: vec![] };
        return DiscoveryResult::with_defs(stmt, branch_info.incoming_defs.clone());
    }

    // Build loop state from loop variables
    let mut final_defs = branch_info.incoming_defs.clone();
    let (state_var_names, state_types, updated_exprs): (Vec<_>, Vec<_>, Vec<_>) =
        loop_var_names.iter()
            .map(|name| {
                // Get the initial temp from pre_header_defs (the value before entering the loop)
                let initial_temp = branch_info.pre_header_defs.get(name).unwrap();

                // Get type from the registry
                let ty = ctx.registry.get_type(*initial_temp)
                    .cloned()
                    .unwrap_or_else(|| panic!("BUG: No type for loop variable '{}' (temp {})", name, initial_temp));

                // Allocate a new temp for the result (post-loop value)
                let result_temp = ctx.registry.alloc_local(name.clone(), ty.clone());
                final_defs.insert(name.clone(), result_temp);

                // Updated value: just reference the variable name (which gets updated in body)
                // The body assigns to `name`, so at the end of the body, `name` has the new value
                let updated_expr = Expression::Var(name.clone());

                (name.clone(), ty, updated_expr)
            })
            .fold((vec![], vec![], vec![]), |mut acc, (sv, ty, upd)| {
                acc.0.push(sv);
                acc.1.push(ty);
                acc.2.push(upd);
                acc
            });

    // Build body block with updated state as result
    let body_block = Block::new(
        flatten_to_stmts(body_result.statement),
        results_to_expr(updated_exprs),
    );

    let while_expr = Expression::WhileExpr {
        condition: condition_block,
        body: body_block,
    };

    // Build the pattern from state variable names (using shadowing - same names)
    let pattern = if state_var_names.len() == 1 {
        LetPattern::Single(state_var_names.into_iter().next().unwrap())
    } else {
        LetPattern::Tuple(state_var_names)
    };

    let stmt = Statement::Let {
        pattern,
        value: while_expr,
        types: state_types,
    };

    DiscoveryResult::with_defs(stmt, final_defs)
}

/// Extract only the statements from `header` that are needed to compute `cond_name`.
fn extract_condition_dependencies(
    header: &Statement,
    cond_name: &str,
    registry: &VariableRegistry,
) -> Statement {
    let stmts = flatten_to_stmts(header.clone());
    if stmts.is_empty() {
        return Statement::default();
    }

    // Build a map from name -> statement index that defines it
    let mut def_map: BTreeMap<String, usize> = BTreeMap::new();
    for (idx, stmt) in stmts.iter().enumerate() {
        for name in get_defined_names(stmt) {
            def_map.insert(name, idx);
        }
    }

    // Backward pass: find all statements needed to compute cond_name
    let mut needed: BTreeSet<usize> = BTreeSet::new();
    let mut worklist: Vec<String> = vec![cond_name.to_string()];

    while let Some(name) = worklist.pop() {
        if let Some(&idx) = def_map.get(&name) {
            if needed.insert(idx) {
                for used_name in get_used_names(&stmts[idx], registry) {
                    worklist.push(used_name);
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

/// Get the names defined by a statement
fn get_defined_names(stmt: &Statement) -> Vec<String> {
    match stmt {
        Statement::Let { pattern, .. } => pattern.names().iter().map(|s| s.to_string()).collect(),
        _ => vec![],
    }
}

/// Check if a variable name is an SSA temporary (e.g., "t82", "t123")
/// SSA temporaries are generated during bytecode translation and shouldn't be
/// carried as loop state - they're local to each basic block.
fn is_ssa_temporary(name: &str) -> bool {
    // SSA temps have format "t" followed by digits only
    if let Some(suffix) = name.strip_prefix('t') {
        suffix.chars().all(|c| c.is_ascii_digit()) && !suffix.is_empty()
    } else {
        false
    }
}

/// Get the names used by a statement's expressions
fn get_used_names(stmt: &Statement, _registry: &VariableRegistry) -> Vec<String> {
    let mut names = Vec::new();
    for expr in stmt.iter_expressions() {
        names.extend(expr.collect_vars());
    }
    names
}

/// Find variables that are used before being defined in a statement.
/// These are "free variables" that need values from outside (previous iteration for loops).
///
/// The algorithm walks statements in execution order, tracking which variables
/// have been defined. When a variable is used but not yet defined, it's added
/// to the result set. Nested blocks (IfExpr, WhileExpr) are handled by
/// recursively computing their free variables.
fn get_used_before_defined(stmt: &Statement) -> BTreeSet<String> {
    let mut defined: BTreeSet<String> = BTreeSet::new();
    let mut free_vars: BTreeSet<String> = BTreeSet::new();
    collect_free_vars_stmt(stmt, &mut defined, &mut free_vars);
    free_vars
}

/// Collect free variables from a statement, updating the defined set.
fn collect_free_vars_stmt(
    stmt: &Statement,
    defined: &mut BTreeSet<String>,
    free_vars: &mut BTreeSet<String>,
) {
    match stmt {
        Statement::Let { pattern, value, .. } => {
            // First: collect free vars from the value expression
            collect_free_vars_expr(value, defined, free_vars);
            // Then: mark the pattern names as defined (shadowing)
            for name in pattern.names() {
                defined.insert(name.to_string());
            }
        }
        Statement::Sequence(stmts) => {
            for s in stmts {
                collect_free_vars_stmt(s, defined, free_vars);
            }
        }
        Statement::Return { values } => {
            for expr in values {
                collect_free_vars_expr(expr, defined, free_vars);
            }
        }
        Statement::Abort { code } => {
            collect_free_vars_expr(code, defined, free_vars);
        }
        Statement::UpdateField { target, new_value, .. } => {
            collect_free_vars_expr(target, defined, free_vars);
            collect_free_vars_expr(new_value, defined, free_vars);
        }
        Statement::UpdateVectorElement { target, index, new_value } => {
            collect_free_vars_expr(target, defined, free_vars);
            collect_free_vars_expr(index, defined, free_vars);
            collect_free_vars_expr(new_value, defined, free_vars);
        }
        Statement::Requires { condition } | Statement::Ensures { condition } => {
            collect_free_vars_expr(condition, defined, free_vars);
        }
    }
}

/// Collect free variables from an expression.
/// For nested blocks (IfExpr, WhileExpr), we compute their free variables
/// but don't let their internal definitions escape to the outer scope.
fn collect_free_vars_expr(
    expr: &Expression,
    defined: &BTreeSet<String>,
    free_vars: &mut BTreeSet<String>,
) {
    match expr {
        Expression::Var(name) => {
            if !defined.contains(name) {
                free_vars.insert(name.clone());
            }
        }
        Expression::IfExpr { condition, then_block, else_block } => {
            // Condition is evaluated in current scope
            collect_free_vars_expr(condition, defined, free_vars);
            // Each branch has its own scope (definitions don't escape)
            collect_free_vars_block(then_block, defined, free_vars);
            collect_free_vars_block(else_block, defined, free_vars);
        }
        Expression::WhileExpr { condition, body } => {
            // Derive loop state variables from body result
            let state_vars: Vec<String> = body.result.iter_vars().map(|s| s.to_string()).collect();
            // Initial values reference current scope (same variable names)
            for var in &state_vars {
                if !defined.contains(var) {
                    free_vars.insert(var.clone());
                }
            }
            // Condition and body have loop variables in scope
            let mut loop_scope = defined.clone();
            for var in &state_vars {
                loop_scope.insert(var.clone());
            }
            collect_free_vars_block(condition, &loop_scope, free_vars);
            collect_free_vars_block(body, &loop_scope, free_vars);
        }
        Expression::Call { args, .. } => {
            for arg in args {
                collect_free_vars_expr(arg, defined, free_vars);
            }
        }
        Expression::BinOp { lhs, rhs, .. } => {
            collect_free_vars_expr(lhs, defined, free_vars);
            collect_free_vars_expr(rhs, defined, free_vars);
        }
        Expression::UnOp { operand, .. } => {
            collect_free_vars_expr(operand, defined, free_vars);
        }
        Expression::FieldAccess { operand, .. } => {
            collect_free_vars_expr(operand, defined, free_vars);
        }
        Expression::Unpack { operand, .. } => {
            collect_free_vars_expr(operand, defined, free_vars);
        }
        Expression::Pack { fields, .. } => {
            for field_expr in fields {
                collect_free_vars_expr(field_expr, defined, free_vars);
            }
        }
        Expression::VecOp { operands, .. } => {
            for operand in operands {
                collect_free_vars_expr(operand, defined, free_vars);
            }
        }
        Expression::Tuple(exprs) => {
            for e in exprs {
                collect_free_vars_expr(e, defined, free_vars);
            }
        }
        Expression::Cast { value, .. } => {
            collect_free_vars_expr(value, defined, free_vars);
        }
        // Constants have no free variables
        Expression::Constant(_) => {}
    }
}

/// Collect free variables from a block.
/// The block's internal definitions don't escape to the outer scope.
fn collect_free_vars_block(
    block: &Block,
    outer_defined: &BTreeSet<String>,
    free_vars: &mut BTreeSet<String>,
) {
    let mut block_defined = outer_defined.clone();
    for stmt in &block.statements {
        collect_free_vars_stmt(stmt, &mut block_defined, free_vars);
    }
    collect_free_vars_expr(&block.result, &block_defined, free_vars);
}

/// Check if a statement is essentially a while loop
fn is_essentially_while(stmt: &Statement) -> bool {
    match stmt {
        Statement::Let { value: Expression::WhileExpr { .. }, .. } => true,
        Statement::Sequence(stmts) => stmts.last().map(is_essentially_while).unwrap_or(false),
        _ => false,
    }
}
