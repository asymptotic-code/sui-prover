// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Computation of phi-nodes for control flow merge points.
//!
//! This module analyzes control flow structures (loops and if/else) to identify
//! variables that need phi-nodes at merge points. For loops, these are "loop-carried"
//! variables (read and written within the loop). For if/else, these are variables
//! with different values from each branch.
//!
//! The actual phi-node values will be computed during bytecode-to-IR translation
//! when we have the SSA temp mappings available.

use crate::control_flow_reconstruction::types::{StructuredBlock, LoopPhiVariable, IfPhiVariable};
use crate::stackless_bytecode::{Bytecode, Operation};
use std::collections::{BTreeSet, BTreeMap};

/// Analyzes a loop body to identify loop-carried variables.
///
/// A variable is loop-carried if:
/// 1. It's read BEFORE being written in the loop body (uses value from previous iteration)
/// 2. It's written in the loop body (updated for next iteration)
///
/// Variables that are only written then read (loop-local temporaries) are NOT loop-carried.
///
/// Note: This computes placeholder phi-nodes with initial_value == updated_value == temp.
/// The actual SSA values will be filled in during IR translation.
pub fn identify_loop_carried_variables(
    body: &StructuredBlock,
    bytecode: &[Bytecode],
) -> Vec<LoopPhiVariable> {
    // Collect all offsets in the loop body in order
    let mut body_offsets = Vec::new();
    collect_offsets_ordered(body, &mut body_offsets);
    body_offsets.sort_unstable();

    log::debug!("=== Loop Phi Variable Analysis ===");
    log::debug!("Loop body offsets (ordered): {:?}", body_offsets);

    // Track first read and first write positions for each temp
    use std::collections::HashMap;
    let mut first_read: HashMap<usize, usize> = HashMap::new();
    let mut first_write: HashMap<usize, usize> = HashMap::new();

    for (position, &offset) in body_offsets.iter().enumerate() {
        if let Some(bc) = bytecode.get(offset as usize) {
            let (srcs, dests) = get_bytecode_vars(bc);
            log::debug!("  Position {}, Offset {}: {:?} -> reads: {:?}, writes: {:?}",
                position, offset, bc, srcs, dests);

            // Record first read position
            for src in srcs {
                first_read.entry(src).or_insert(position);
            }

            // Record first write position
            for dest in dests {
                first_write.entry(dest).or_insert(position);
            }
        }
    }

    log::debug!("First read positions: {:?}", first_read);
    log::debug!("First write positions: {:?}", first_write);

    // A variable is loop-carried if it's read before being written
    // Collect them first, then sort by temp index for deterministic ordering
    let mut loop_carried_temps = Vec::new();
    for (&temp, &read_pos) in &first_read {
        if let Some(&write_pos) = first_write.get(&temp) {
            // Variable is both read and written
            if read_pos < write_pos {
                // Read happens BEFORE write - this is loop-carried (uses value from previous iteration)
                log::debug!("  -> Loop-carried variable identified: temp {} (read at {}, written at {})",
                    temp, read_pos, write_pos);
                loop_carried_temps.push(temp);
            } else {
                // Write happens first - this is a loop-local temporary
                log::debug!("  -> Loop-local temporary (NOT loop-carried): temp {} (written at {}, then read at {})",
                    temp, write_pos, read_pos);
            }
        }
    }

    // Sort by temp index for deterministic ordering
    loop_carried_temps.sort_unstable();

    let mut loop_carried = Vec::new();
    for temp in loop_carried_temps {
        loop_carried.push(LoopPhiVariable::new(temp, temp, temp));
    }

    log::debug!("Final loop-carried variables: {:?}", loop_carried.iter().map(|v| v.temp).collect::<Vec<_>>());
    log::debug!("=== End Loop Phi Analysis ===\n");

    loop_carried
}

/// Collect all bytecode offsets within a structured block (ordered)
fn collect_offsets_ordered(block: &StructuredBlock, offsets: &mut Vec<u16>) {
    match block {
        StructuredBlock::Basic { lower, upper } => {
            for i in *lower..=*upper {
                offsets.push(i);
            }
        }
        StructuredBlock::IfThenElse { then_branch, else_branch, .. } => {
            collect_offsets_ordered(then_branch, offsets);
            if let Some(eb) = else_branch {
                collect_offsets_ordered(eb, offsets);
            }
        }
        StructuredBlock::While { condition_body, body, .. } => {
            collect_offsets_ordered(condition_body, offsets);
            collect_offsets_ordered(body, offsets);
        }
        StructuredBlock::Seq(blocks) => {
            for b in blocks {
                collect_offsets_ordered(b, offsets);
            }
        }
        StructuredBlock::IfElseChain { branches, else_branch } => {
            for (_, body) in branches {
                collect_offsets_ordered(body, offsets);
            }
            if let Some(eb) = else_branch {
                collect_offsets_ordered(eb, offsets);
            }
        }
    }
}

/// Collect all bytecode offsets within a structured block
fn collect_offsets(block: &StructuredBlock, offsets: &mut BTreeSet<u16>) {
    match block {
        StructuredBlock::Basic { lower, upper } => {
            for i in *lower..=*upper {
                offsets.insert(i);
            }
        }
        StructuredBlock::IfThenElse { then_branch, else_branch, .. } => {
            collect_offsets(then_branch, offsets);
            if let Some(eb) = else_branch {
                collect_offsets(eb, offsets);
            }
        }
        StructuredBlock::While { condition_body, body, .. } => {
            collect_offsets(condition_body, offsets);
            collect_offsets(body, offsets);
        }
        StructuredBlock::Seq(blocks) => {
            for b in blocks {
                collect_offsets(b, offsets);
            }
        }
        StructuredBlock::IfElseChain { branches, else_branch } => {
            for (_, body) in branches {
                collect_offsets(body, offsets);
            }
            if let Some(eb) = else_branch {
                collect_offsets(eb, offsets);
            }
        }
    }
}

/// Extract source and destination temps from a bytecode instruction
fn get_bytecode_vars(bytecode: &Bytecode) -> (Vec<usize>, Vec<usize>) {
    match bytecode {
        Bytecode::Call(_, dests, _, srcs, _) => (srcs.clone(), dests.clone()),
        Bytecode::Load(_, dest, _) => (vec![], vec![*dest]),
        Bytecode::Assign(_, dest, src, _) => (vec![*src], vec![*dest]),
        Bytecode::Ret(_, srcs) => (srcs.clone(), vec![]),
        Bytecode::Abort(_, src) => (vec![*src], vec![]),
        Bytecode::Branch(_, _, _, cond) => (vec![*cond], vec![]),
        _ => (vec![], vec![]),
    }
}

/// Comprehensive assignment tracking that handles nested control flow.
/// Returns a mapping from variable -> exit value at the end of the block.
///
/// This handles:
/// - Direct assignments (x := y)
/// - Call operations (x := f(...))
/// - Nested If statements with phi-merging
/// - While loops (conservatively marks as "written but unknown value")
/// - Aborts/Returns (block doesn't reach end)
///
/// The key difference from top-level scanning: we recursively process nested control flow
/// and determine the final value of each variable when control exits the block.
fn scan_all_assignments(
    block: &StructuredBlock,
    bytecode: &[Bytecode],
) -> BTreeMap<usize, usize> {
    let mut assignments: BTreeMap<usize, usize> = BTreeMap::new();
    scan_block_recursive(block, bytecode, &mut assignments);
    assignments
}

fn scan_block_recursive(
    block: &StructuredBlock,
    bytecode: &[Bytecode],
    assignments: &mut BTreeMap<usize, usize>,
) {
    match block {
        StructuredBlock::Basic { lower, upper } => {
            // Scan all bytecode in this basic block
            for offset in *lower..=*upper {
                if let Some(bc) = bytecode.get(offset as usize) {
                    match bc {
                        Bytecode::Assign(_, dst, src, _) => {
                            // Direct assignment: track source value
                            assignments.insert(*dst, *src);
                        }
                        Bytecode::Call(_, dests, op, _, _) => {
                            // Call operation: mark as "written to itself" (can't track source)
                            // This indicates the variable is defined but we don't know the value
                            if !is_side_effecting_op(op) {
                                for &dest in dests {
                                    assignments.insert(dest, dest);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        StructuredBlock::Seq(blocks) => {
            // Process blocks in sequence, later assignments override earlier ones
            for b in blocks {
                scan_block_recursive(b, bytecode, assignments);
            }
        }

        StructuredBlock::IfThenElse { then_branch, else_branch, .. } => {
            // For nested If, we need to compute what variables are written in each branch
            let mut then_assigns = BTreeMap::new();
            scan_block_recursive(then_branch, bytecode, &mut then_assigns);

            let mut else_assigns = BTreeMap::new();
            if let Some(eb) = else_branch {
                scan_block_recursive(eb, bytecode, &mut else_assigns);
            }

            // Collect all variables written in either branch
            let mut all_written = BTreeSet::new();
            all_written.extend(then_assigns.keys());
            all_written.extend(else_assigns.keys());

            // For each written variable, determine exit value:
            // - If both branches write it with same value -> use that value
            // - If both branches write it with different values -> mark as "written to itself" (phi-merge needed)
            // - If only one branch writes it -> mark as "written to itself" (conditional assignment)
            for &var in &all_written {
                let then_val = then_assigns.get(&var).copied();
                let else_val = else_assigns.get(&var).copied();

                match (then_val, else_val) {
                    (Some(tv), Some(ev)) if tv == ev => {
                        // Both branches assign same value
                        assignments.insert(var, tv);
                    }
                    _ => {
                        // Different values or only one branch assigns
                        // Mark as "self-assignment" to indicate it's written but value unknown
                        assignments.insert(var, var);
                    }
                }
            }
        }

        StructuredBlock::While { .. } => {
            // For loops, we conservatively assume any variable might be modified
            // but we can't determine the exit value, so we don't track anything.
            // This is safe because loop phi-nodes are handled separately.
        }

        StructuredBlock::IfElseChain { branches, else_branch } => {
            // Similar to IfThenElse but with multiple branches
            let mut all_branch_assigns = Vec::new();

            for (_, body) in branches {
                let mut branch_assigns = BTreeMap::new();
                scan_block_recursive(body, bytecode, &mut branch_assigns);
                all_branch_assigns.push(branch_assigns);
            }

            if let Some(eb) = else_branch {
                let mut else_assigns = BTreeMap::new();
                scan_block_recursive(eb, bytecode, &mut else_assigns);
                all_branch_assigns.push(else_assigns);
            }

            // Collect all variables written in any branch
            let mut all_written = BTreeSet::new();
            for branch_assigns in &all_branch_assigns {
                all_written.extend(branch_assigns.keys());
            }

            // For each variable, check if all branches assign the same value
            for &var in &all_written {
                let values: Vec<_> = all_branch_assigns.iter()
                    .filter_map(|ba| ba.get(&var).copied())
                    .collect();

                if !values.is_empty() && values.iter().all(|&v| v == values[0]) {
                    // All branches that write this variable use the same value
                    assignments.insert(var, values[0]);
                } else {
                    // Different values or not all branches write it
                    assignments.insert(var, var);
                }
            }
        }
    }
}

/// Check if an operation has side effects (adapted from conditional_merge_insertion)
fn is_side_effecting_op(op: &Operation) -> bool {
    use Operation::*;
    matches!(
        op,
        MoveTo(..)
            | MoveFrom(..)
            | BorrowGlobal(..)
            | GetGlobal(..)
            | WriteRef
            | Havoc(..)
            | Stop
            | Uninit
            | Destroy
            | EmitEvent
            | EventStoreDiverge
    )
}

/// Check if a structured block terminates (ends with Abort or Ret)
fn block_terminates(block: &StructuredBlock, bytecode: &[Bytecode]) -> bool {
    match block {
        StructuredBlock::Basic { lower: _, upper } => {
            // Check if the last bytecode in this block terminates
            if let Some(bc) = bytecode.get(*upper as usize) {
                matches!(bc, Bytecode::Ret(..) | Bytecode::Abort(..))
            } else {
                false
            }
        }
        StructuredBlock::Seq(blocks) => {
            // Check if the last block in the sequence terminates
            blocks.last().map_or(false, |b| block_terminates(b, bytecode))
        }
        StructuredBlock::IfThenElse { then_branch, else_branch, .. } => {
            // If terminates if both branches terminate
            let then_term = block_terminates(then_branch, bytecode);
            let else_term = else_branch.as_ref().map_or(false, |b| block_terminates(b, bytecode));
            then_term && else_term
        }
        StructuredBlock::While { .. } => {
            // Loops don't terminate normally (they either break or run forever)
            false
        }
        StructuredBlock::IfElseChain { branches, else_branch } => {
            // All branches must terminate
            let all_branches_term = branches.iter().all(|(_, body)| block_terminates(body, bytecode));
            let else_term = else_branch.as_ref().map_or(true, |b| block_terminates(b, bytecode));
            all_branches_term && else_term
        }
    }
}

/// Analyzes if/else branches to identify variables that need phi-nodes at the merge point.
///
/// A variable needs a phi-node if it has different values after the then and else branches.
/// This function scans the bytecode in each branch to extract the actual SSA temp values
/// that are assigned to each variable.
///
/// Instead of using placeholders, we compute the actual then_value and else_value by
/// scanning the bytecode assignments in each branch. This eliminates the need for
/// IR-level phi detection which fails with nested control flow.
///
/// IMPORTANT: If either branch terminates (Abort/Ret), we should NOT create phi-nodes
/// because there's no merge point - the terminating branch doesn't reach the continuation.
pub fn identify_if_phi_variables(
    then_branch: &StructuredBlock,
    else_branch: Option<&StructuredBlock>,
    bytecode: &[Bytecode],
) -> Vec<IfPhiVariable> {
    log::debug!("=== If Phi Variable Analysis (Bytecode Level) ===");

    // Check if branches terminate
    let then_terminates = block_terminates(then_branch, bytecode);
    let else_terminates = else_branch.as_ref().map_or(false, |b| block_terminates(b, bytecode));

    log::debug!("Then-branch terminates: {}", then_terminates);
    log::debug!("Else-branch terminates: {}", else_terminates);

    // If either branch terminates, no phi-nodes needed (one-branch-terminates pattern)
    if then_terminates || else_terminates {
        log::debug!("One or both branches terminate - no phi-nodes needed");
        log::debug!("=== End If Phi Analysis ===\n");
        return vec![];
    }

    // Scan ALL assignments in each branch, including nested control flow
    // This returns exit values for variables when control leaves each branch
    let then_assignments = scan_all_assignments(then_branch, bytecode);
    log::debug!("Then-branch assignments (with nesting): {:?}", then_assignments);

    let else_assignments = if let Some(eb) = else_branch {
        let assignments = scan_all_assignments(eb, bytecode);
        log::debug!("Else-branch assignments (with nesting): {:?}", assignments);
        assignments
    } else {
        log::debug!("No else-branch");
        BTreeMap::new()
    };

    // CRITICAL: Only create phi-nodes for variables written in BOTH branches.
    // Variables only written in one branch don't need merging - they're undefined
    // in the other branch and would cause "Unknown identifier" errors.
    let mut all_written: BTreeSet<usize> = BTreeSet::new();
    all_written.extend(then_assignments.keys());
    all_written.extend(else_assignments.keys());

    let mut phi_vars = Vec::new();

    for &temp in &all_written {
        // Skip variables not written in both branches
        if !then_assignments.contains_key(&temp) || !else_assignments.contains_key(&temp) {
            log::debug!("Skipping temp {} (not written in both branches)", temp);
            continue;
        }

        // Get exit values from each branch
        // Note: scan_all_assignments returns var->var for "written but value unknown"
        let then_value = then_assignments.get(&temp).copied().unwrap();
        let else_value = else_assignments.get(&temp).copied().unwrap();

        log::debug!(
            "Analyzing temp {}: then_value={} else_value={}",
            temp, then_value, else_value
        );

        // Decision logic for phi-node creation:
        //
        // Case 1: Both branches assign SAME concrete value (e.g., both assign from t5)
        //         -> No phi needed, value is deterministic
        //
        // Case 2: Both branches have self-assignment (var->var from Call/nested-If)
        //         -> Skip phi for now, let IR translator handle it
        //         (This avoids creating phi-nodes we can't populate correctly)
        //
        // Case 3: Different values (including one concrete, one self)
        //         -> Create phi-node

        let then_is_self = then_value == temp;
        let else_is_self = else_value == temp;

        // Self-assignment (var->var) indicates value comes from Call/nested-If.
        // We still create the phi-node but mark it with placeholder values.
        // The IR translator will scan the translated statements to extract actual values.
        // This follows the same pattern as loop phi variables (see line 26-27 above).

        if then_value == else_value && !then_is_self {
            // Both branches assign the same concrete value - no phi needed
            log::debug!("  -> Skipping phi-node (same concrete value in both branches: {})", then_value);
            continue;
        }

        // Create phi-node if:
        // 1. Values differ (concrete or placeholder), OR
        // 2. Both are self-assignments (both branches assign via Call/nested-If)
        log::debug!("  -> Creating phi-node: then={} (self={}) else={} (self={})",
            then_value, then_is_self, else_value, else_is_self);
        phi_vars.push(IfPhiVariable::new(temp, then_value, else_value));
    }

    log::debug!("Final phi variables: {:?}", phi_vars.iter().map(|v| (v.temp, v.then_value, v.else_value)).collect::<Vec<_>>());
    log::debug!("=== End If Phi Analysis ===\n");

    phi_vars
}

/// Compute phi-variables for all control flow merge points in a structured block tree.
/// This modifies While and IfThenElse blocks in-place to populate their phi_variables fields.
pub fn compute_phi_variables(block: StructuredBlock, bytecode: &[Bytecode]) -> StructuredBlock {
    match block {
        StructuredBlock::While { cond_at, cond_temp, condition_body, body, .. } => {
            // Recursively process nested structures first
            let processed_condition = Box::new(compute_phi_variables(*condition_body, bytecode));
            let processed_body = Box::new(compute_phi_variables(*body, bytecode));

            // Compute phi-variables for this loop
            let phi_variables = identify_loop_carried_variables(&processed_body, bytecode);

            StructuredBlock::While {
                cond_at,
                cond_temp,
                condition_body: processed_condition,
                body: processed_body,
                phi_variables,
            }
        }
        StructuredBlock::IfThenElse { cond_at, cond_temp, then_branch, else_branch, .. } => {
            // Recursively process nested structures first
            let processed_then = Box::new(compute_phi_variables(*then_branch, bytecode));
            let processed_else = else_branch.map(|b| Box::new(compute_phi_variables(*b, bytecode)));

            // Compute phi-variables for this if/else
            let phi_variables = identify_if_phi_variables(
                &processed_then,
                processed_else.as_deref(),
                bytecode
            );

            StructuredBlock::IfThenElse {
                cond_at,
                cond_temp,
                then_branch: processed_then,
                else_branch: processed_else,
                phi_variables,
            }
        }
        StructuredBlock::Seq(blocks) => {
            StructuredBlock::Seq(
                blocks.into_iter()
                    .map(|b| compute_phi_variables(b, bytecode))
                    .collect()
            )
        }
        StructuredBlock::IfElseChain { branches, else_branch } => {
            StructuredBlock::IfElseChain {
                branches: branches.into_iter()
                    .map(|(cond, body)| (cond, Box::new(compute_phi_variables(*body, bytecode))))
                    .collect(),
                else_branch: else_branch.map(|b| Box::new(compute_phi_variables(*b, bytecode))),
            }
        }
        other => other,
    }
}
