// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Structure Discovery Phase - Builds Statement IR directly
//!
//! Discovers control flow structure (if/else/while) from CFG and builds Statement IR.
//! Uses immediate post-dominator (IPD) analysis to find merge points.

use super::helpers::*;
use super::DiscoveryContext;
use crate::translation::statement_translator;
use intermediate_theorem_format::{Expression, LoopCondition, Statement, TempId};
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Label};
use move_stackless_bytecode::stackless_control_flow_graph::BlockId;
use crate::control_flow_reconstruction::phi_computation::{compute_loop_vars, compute_phi_at_merge};

/// Information about a branch instruction
#[derive(Debug, Clone)]
struct BranchInfo {
    then_label: Label,
    else_label: Label,
    cond_temp: TempId,
    header: Statement,
    start: BlockId,
    stop: BlockId
}

/// Find immediate post-dominator of a block using the library function
fn find_immediate_post_dominator(ctx: &DiscoveryContext, block: BlockId) -> Option<BlockId> {
    use move_stackless_bytecode::stackless_control_flow_graph::StacklessControlFlowGraph;
    StacklessControlFlowGraph::find_immediate_post_dominator(&ctx.back_cfg, block)
}

/// Discover structure and build Statement IR directly
thread_local! {
    static CALL_HISTORY: std::cell::RefCell<std::collections::HashSet<(BlockId, BlockId)>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
    static CACHE: std::cell::RefCell<std::collections::HashMap<(BlockId, BlockId), Statement>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

fn discover_structure_impl(
    ctx: &mut DiscoveryContext,
    start: BlockId,
    stop: BlockId,
    depth: &mut usize,
) -> Statement {
    *depth += 1;
    eprintln!("[DEPTH {}] discover_structure(start={}, stop={})", *depth, start, stop);

    if *depth > 200 {
        eprintln!("RECURSION EXCEEDED! Dumping call history:");
        CALL_HISTORY.with(|history| {
            for (s, e) in history.borrow().iter() {
                eprintln!("  - ({}, {})", s, e);
            }
        });
        panic!("Recursion depth exceeded 200: start={}, stop={}, this indicates infinite recursion", start, stop);
    }

    // Check if we're in a recursive call with the same parameters
    let call_id = (start, stop);
    let already_processing = CALL_HISTORY.with(|history| {
        !history.borrow_mut().insert(call_id)
    });
    if already_processing {
        eprintln!("WARNING: Re-entering discover_structure({}, {}) - returning empty to break cycle", start, stop);
        *depth -= 1;
        return Statement::default();
    }

    // Check cache first
    let cached = CACHE.with(|cache| cache.borrow().get(&call_id).cloned());
    if let Some(cached_result) = cached {
        CALL_HISTORY.with(|history| history.borrow_mut().remove(&call_id));
        *depth -= 1;
        return cached_result;
    }

    // Base case: if start == stop, return immediately
    if start == stop {
        CALL_HISTORY.with(|history| history.borrow_mut().remove(&call_id));
        *depth -= 1;
        return Statement::default();
    }

    let mut statement = Statement::default();
    let mut cursor = start;

    while cursor != stop {
        let (lower, upper) = match block_bounds(&ctx.forward_cfg, cursor) {
                Some(bounds) => bounds,
                None => {
                    cursor = *ctx.forward_cfg.successors(cursor).first().unwrap_or(&stop);
                    continue;
                }
            };

            // Check for branch instruction
            if let Bytecode::Branch(_, tlabel, elabel, cond_temp) = &ctx.code[upper as usize] {
                let header = statement_translator::translate_range(ctx, lower..=upper);
                let branch_info = BranchInfo {
                    then_label: *tlabel,
                    else_label: *elabel,
                    cond_temp: *cond_temp as TempId,
                    header: header.clone(),
                    start,
                    stop
                };
                let branch = handle_branch(ctx, &mut cursor, branch_info, depth);
                statement = statement.combine(header.combine(branch));
                continue;
            }

            // Abort edge is always second
            cursor = *ctx.forward_cfg.successors(cursor).first().unwrap_or(&stop);
            statement = statement.combine(statement_translator::translate_range(ctx, lower..=upper));
        }

    // Cache the result before returning
    CACHE.with(|cache| cache.borrow_mut().insert(call_id, statement.clone()));
    CALL_HISTORY.with(|history| history.borrow_mut().remove(&call_id));
    *depth -= 1;
    statement
}

pub fn discover_structure(
    ctx: &mut DiscoveryContext,
    start: BlockId,
    stop: BlockId,
) -> Statement {
    // Clear caches at the start of each function
    CACHE.with(|cache| cache.borrow_mut().clear());
    CALL_HISTORY.with(|history| history.borrow_mut().clear());

    let mut depth = 0;
    discover_structure_impl(ctx, start, stop, &mut depth)
}

/// Handle branch instruction - build If or While statement
fn handle_branch(
    ctx: &mut DiscoveryContext,
    cursor: &mut BlockId,
    branch_info: BranchInfo,
    depth: &mut usize,
) -> Statement {
    let then_block = resolve_label_block(ctx, branch_info.then_label)
        .expect("Loop then branch must resolve to a valid block");
    let else_block = resolve_label_block(ctx, branch_info.else_label)
        .expect("Loop else branch must resolve to a valid block");
    // A back edge occurs when the target equals the current block (self-loop)
    // or when the target dominates the current block (the current block is dominated by the target)
    let then_jumps_back = then_block == *cursor || ctx.forward_dom.is_dominated_by(*cursor, then_block);
    let else_jumps_back = else_block == *cursor || ctx.forward_dom.is_dominated_by(*cursor, else_block);

    if then_jumps_back || else_jumps_back {
        // While statement
        let (loop_body, loop_exit) = if then_jumps_back {
            (then_block, else_block)
        } else {
            (else_block, then_block)
        };
        let loop_header = *cursor;
        *cursor = loop_exit;
        let body = Box::new(discover_structure_impl(ctx, loop_body, loop_header, depth));
        Statement::While {
            condition: LoopCondition {
                recompute: Box::new(branch_info.header.clone()),
                condition_var: branch_info.cond_temp,
            },
            loop_vars: compute_loop_vars(&body, ctx.registry),
            body,
        }
    } else {
        // If statement - find merge point using immediate post-dominator
        // The immediate post-dominator is the immediate dominator in the backward CFG
        let merge_block = find_immediate_post_dominator(ctx, *cursor).unwrap_or(branch_info.stop);

        // Check for degenerate case: if one branch goes back to the start of the current region
        // This indicates a loop that wasn't detected by the dominance check
        if (then_block == branch_info.start || else_block == branch_info.start) && merge_block == branch_info.stop {
            // Treat this as a loop
            let (loop_body, loop_exit) = if then_block == branch_info.start {
                (then_block, else_block)
            } else {
                (else_block, then_block)
            };
            let loop_header = *cursor;
            *cursor = loop_exit;
            let body = Box::new(discover_structure_impl(ctx, loop_body, loop_header, depth));
            return Statement::While {
                condition: LoopCondition {
                    recompute: Box::new(branch_info.header.clone()),
                    condition_var: branch_info.cond_temp,
                },
                loop_vars: compute_loop_vars(&body, ctx.registry),
                body,
            };
        }

        *cursor = merge_block;
        eprintln!("[DEPTH {}] IF: then_block={}, else_block={}, merge={}", *depth, then_block, else_block, merge_block);
        let then_branch = Box::new(discover_structure_impl(ctx, then_block, *cursor, depth));
        let else_branch = Box::new(discover_structure_impl(ctx, else_block, *cursor, depth));
        Statement::If {
            condition: Expression::Temporary(branch_info.cond_temp),
            phi_vars: compute_phi_at_merge(&then_branch, &else_branch, ctx.registry),
            then_branch,
            else_branch,
        }
    }
}
