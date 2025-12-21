// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Structure Discovery - Reconstructs structured control flow from CFG

use super::helpers::{block_bounds, resolve_label_block};
use super::DiscoveryContext;
use crate::translation::ir_translator;
use intermediate_theorem_format::{IRNode, UnOp};
use move_binary_format::file_format::CodeOffset;
use move_stackless_bytecode::loop_analysis::LoopAnnotation;
use move_stackless_bytecode::move_loop_invariants::TargetedLoopInfo;
use move_stackless_bytecode::stackless_bytecode::{AttrId, Bytecode, Label, Operation};
use move_stackless_bytecode::stackless_control_flow_graph::BlockId;
use std::collections::BTreeSet;

pub fn reconstruct_function(mut ctx: DiscoveryContext) -> IRNode {
    let entry = ctx.forward_cfg.entry_block();
    let exit = ctx.forward_cfg.exit_block();
    discover_region(&mut ctx, entry, exit)
}

fn discover_region(ctx: &mut DiscoveryContext, start: BlockId, stop: BlockId) -> IRNode {
    let mut node = IRNode::default();
    let mut cursor = start;

    while cursor != stop {
        let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, cursor) else {
            cursor = next_block(ctx, cursor, stop);
            continue;
        };

        // Skip blocks ending with Stop - these are dummy invariant-checking blocks
        // created by loop analysis that redirect back edges. They don't contain
        // real code to translate.
        if is_stop_block(ctx, upper) {
            cursor = next_block(ctx, cursor, stop);
            continue;
        }

        // Check if this block is a loop header using LoopAnnotation
        // This is the primary way to detect loops when loop analysis has transformed the bytecode
        let loop_label = find_label_in_block(ctx, cursor);

        if let Some(label) = loop_label {
            if is_loop_header(ctx, label) {
                // This is a loop header identified by loop analysis
                // Find the branch that controls the loop
                if let Some((loop_node, exit_block)) = handle_loop_header(ctx, cursor, lower, upper, label, stop) {
                    node = node.combine(loop_node);
                    cursor = exit_block;
                    continue;
                }
            }
        }

        if let Bytecode::Branch(_, then_label, else_label, cond_temp) =
            ctx.target.get_bytecode()[upper as usize].clone()
        {
            let cond_name = ir_translator::temp_id(ctx, cond_temp);
            let then_block = resolve_label_block(ctx, then_label).expect("then label must resolve");
            let else_block = resolve_label_block(ctx, else_label).expect("else label must resolve");

            // Check if either branch is a back-edge (loop) - fallback for non-annotated loops
            let then_reaches_cursor = reaches(&ctx.forward_cfg, then_block, cursor, stop);
            let else_reaches_cursor = reaches(&ctx.forward_cfg, else_block, cursor, stop);

            let then_is_back =
                then_block == start
                || ctx.forward_dom.is_dominated_by(cursor, then_block)
                || then_reaches_cursor
                || is_invariant_check_block(ctx, then_block);
            let else_is_back =
                else_block == start
                || ctx.forward_dom.is_dominated_by(cursor, else_block)
                || else_reaches_cursor
                || is_invariant_check_block(ctx, else_block);


            if then_is_back || else_is_back {
                // Find the loop header label to look up invariants
                let loop_label = find_label_in_block(ctx, cursor);
                let func_name = ctx.target.func_env.get_name_str();
                if func_name.contains("get_tick_at_sqrt_price") {
                    eprintln!("LOOP_DETECT: {} found loop at cursor={} loop_label={:?}", func_name, cursor, loop_label);
                    eprintln!("  loop_invariants count: {}", ctx.target.data.loop_invariants.len());
                }

                // Extract loop invariants from LoopAnnotation
                let invariants = loop_label
                    .map(|label| extract_invariants_for_label(ctx, label))
                    .unwrap_or_default();

                // Translate the header block, skipping loop analysis artifacts
                let header = translate_range_skip_loop_artifacts(ctx, lower, upper);
                node = node.combine(header);

                let (body_start, exit_block) = if then_is_back {
                    (then_block, else_block)
                } else {
                    (else_block, then_block)
                };

                // Discover the loop body, which includes everything from body_start back to cursor (exclusive)
                let body_nodes = discover_region(ctx, body_start, cursor);

                // Find the actual condition expression instead of just referencing the variable
                // This ensures the condition is re-evaluated each iteration
                let cond_expr = find_condition_expression(ctx, lower, upper, cond_temp);
                let cond = if !then_is_back {
                    IRNode::UnOp {
                        op: UnOp::Not,
                        operand: Box::new(cond_expr),
                    }
                } else {
                    cond_expr
                };

                let while_node = IRNode::While {
                    cond: Box::new(cond),
                    body: Box::new(body_nodes),
                    vars: vec![], // Phi detection will populate this later
                    invariants,
                };

                node = node.combine(while_node);

                cursor = exit_block;
                continue;
            }

            // Not a loop - regular if-then-else
            let header = ir_translator::translate_range(ctx, lower..=upper);
            node = node.combine(header);

            let merge =
                find_merge_block(ctx, then_block, else_block, stop).unwrap_or(stop);

            let then_ir = discover_region(ctx, then_block, merge);
            let else_ir = discover_region(ctx, else_block, merge);

            node = node.combine(IRNode::If {
                cond: Box::new(IRNode::Var(cond_name)),
                then_branch: Box::new(then_ir),
                else_branch: Box::new(else_ir),
            });

            // Continue at the merge
            cursor = merge;
            continue;
        }

        // Check if this block's successor will loop back to this block or start
        // If so, skip translation and let the loop discovery handle it
        let next = next_block(ctx, cursor, stop);
        if next != stop {
            if let Some((_next_lower, next_upper)) = block_bounds(&ctx.forward_cfg, next) {
                if let Bytecode::Branch(_, then_label, else_label, _) =
                    ctx.target.get_bytecode()[next_upper as usize].clone()
                {
                    let then_block = resolve_label_block(ctx, then_label).expect("then label must resolve");
                    let else_block = resolve_label_block(ctx, else_label).expect("else label must resolve");

                    // Check if next block branches back to current or start
                    let then_loops_back = then_block == cursor || then_block == start;
                    let else_loops_back = else_block == cursor || else_block == start;

                    if then_loops_back || else_loops_back {
                        // Don't translate, just move to next block which will handle the loop
                        cursor = next;
                        continue;
                    }
                }
            }
        }

        node  = node.combine(ir_translator::translate_range(ctx, lower..=upper));

        // Check if this block terminates (Ret or Abort) - if so, stop traversal
        if matches!(
            ctx.target.get_bytecode()[upper as usize],
            Bytecode::Ret(_, _) | Bytecode::Abort(_, _)
        ) {
            break;
        }

        cursor = next;
    }

    node
}

/// Check if a label marks a loop header using the LoopAnnotation.
fn is_loop_header(ctx: &DiscoveryContext, label: Label) -> bool {
    ctx.target
        .get_annotations()
        .get::<LoopAnnotation>()
        .map(|annotation| annotation.fat_loops.contains_key(&label))
        .unwrap_or(false)
}

/// Handle a loop header block identified by LoopAnnotation.
/// Returns the generated While node and the exit block to continue from.
fn handle_loop_header(
    ctx: &mut DiscoveryContext,
    _cursor: BlockId,
    lower: CodeOffset,
    upper: CodeOffset,
    label: Label,
    stop: BlockId,
) -> Option<(IRNode, BlockId)> {
    let func_name = ctx.target.func_env.get_name_str();
    if func_name.contains("get_tick_at_sqrt_price") {
        eprintln!("HANDLE_LOOP: {} label={:?} loop_invariants={}", func_name, label, ctx.target.data.loop_invariants.len());
    }

    // Extract invariants for this loop
    let invariants = extract_invariants_for_label(ctx, label);

    // Extract branch info from header block
    let (then_label, else_label) = {
        let bytecodes = ctx.target.get_bytecode();
        let Bytecode::Branch(_, then_label, else_label, _cond_temp) = &bytecodes[upper as usize] else {
            return None;
        };
        (*then_label, *else_label)
    };

    let then_block = resolve_label_block(ctx, then_label)?;
    let else_block = resolve_label_block(ctx, else_label)?;

    // The invariant check branch leads to a block that eventually has the actual loop condition.
    // We need to find the first branch that leads to either Stop (body) or non-Stop (exit).

    // Look for the loop condition in successor blocks
    // The successor of the invariant check should contain the actual loop condition
    let invariant_merge = find_merge_block(ctx, then_block, else_block, stop)?;

    // The merge block should have the actual loop condition
    let Some((merge_lower, merge_upper)) = block_bounds(&ctx.forward_cfg, invariant_merge) else {
        return None;
    };

    // Extract loop condition branch info
    let (loop_then_label, loop_else_label, cond_temp) = {
        let bytecodes = ctx.target.get_bytecode();
        let Bytecode::Branch(_, loop_then_label, loop_else_label, cond_temp) = &bytecodes[merge_upper as usize] else {
            return None;
        };
        (*loop_then_label, *loop_else_label, *cond_temp)
    };

    let _cond_name = ir_translator::temp_id(ctx, cond_temp);
    let loop_then_block = resolve_label_block(ctx, loop_then_label)?;
    let loop_else_block = resolve_label_block(ctx, loop_else_label)?;

    // Determine which branch is the loop body and which is the exit
    // The EXIT branch leads to the code after the loop (return or continuation)
    // The BODY branch continues with loop body code, eventually returning to header
    //
    // Detection strategies:
    // 1. Exit path may immediately end with Stop (invariant check for re-entry)
    // 2. Exit path may have a successor that ends with Ret (return)
    // 3. Exit path may branch back to loop condition blocks
    //
    // Check if each branch is an exit path
    let then_is_exit = is_invariant_check_block(ctx, loop_then_block) ||
                       block_immediately_ends_with_stop(ctx, loop_then_block) ||
                       has_immediate_return_successor(ctx, loop_then_block);
    let else_is_exit = is_invariant_check_block(ctx, loop_else_block) ||
                       block_immediately_ends_with_stop(ctx, loop_else_block) ||
                       has_immediate_return_successor(ctx, loop_else_block);

    // Determine body and exit based on which is the exit path
    // If then_is_exit, then then branch exits, else branch is body (negate condition)
    // If else_is_exit, then else branch exits, then branch is body (no negate)
    let (body_block, exit_block, negate_cond) = if then_is_exit && !else_is_exit {
        // Then branch exits, else is body - need to negate condition for while
        (loop_else_block, loop_then_block, true)
    } else if else_is_exit && !then_is_exit {
        // Else branch exits, then is body - condition is correct as-is
        (loop_then_block, loop_else_block, false)
    } else {
        // Can't determine - fall back to old behavior
        return None;
    };

    // Translate the header block, skipping loop analysis artifacts (havoc/prop/ensures/requires)
    let header = translate_range_skip_loop_artifacts(ctx, lower, upper);

    // Translate constants and pre-condition setup from merge block
    // These need to be available before the while condition is evaluated
    let merge_setup = translate_constants_and_setup(ctx, merge_lower, merge_upper, cond_temp);

    // Find the condition expression from the merge block
    // The condition is computed by the instruction that defines cond_temp
    let cond_expr = find_condition_expression(ctx, merge_lower, merge_upper, cond_temp);

    // Discover the loop body - explore from body_block until we hit a Stop block
    let body_nodes = discover_loop_body(ctx, body_block, stop);

    // Build the condition expression (negate if needed)
    let cond = if negate_cond {
        IRNode::UnOp {
            op: UnOp::Not,
            operand: Box::new(cond_expr),
        }
    } else {
        cond_expr
    };

    let while_node = IRNode::While {
        cond: Box::new(cond),
        body: Box::new(body_nodes),
        vars: vec![], // Phi detection will populate this later
        invariants,
    };

    // Combine: header -> merge_setup -> while
    Some((header.combine(merge_setup).combine(while_node), exit_block))
}

/// Check if a block has an immediate successor that ends with Ret
/// This is used to identify the loop exit path which leads to return
fn has_immediate_return_successor(ctx: &DiscoveryContext, block: BlockId) -> bool {
    let bytecodes = ctx.target.get_bytecode();

    // Check immediate successors for Ret
    for succ in ctx.forward_cfg.successors(block) {
        if let Some((_, succ_upper)) = block_bounds(&ctx.forward_cfg, *succ) {
            if matches!(bytecodes[succ_upper as usize], Bytecode::Ret(_, _)) {
                return true;
            }
        }
    }

    false
}

/// Check if a block immediately ends with Stop (within 1 hop)
/// This is used to identify the loop exit path which goes directly to the invariant check
fn block_immediately_ends_with_stop(ctx: &DiscoveryContext, block: BlockId) -> bool {
    let Some((_, upper)) = block_bounds(&ctx.forward_cfg, block) else {
        return false;
    };

    // Check if this block directly ends with Stop
    if is_stop_block(ctx, upper) {
        return true;
    }

    // Check if any immediate successor is a Stop block
    for succ in ctx.forward_cfg.successors(block) {
        if let Some((_, succ_upper)) = block_bounds(&ctx.forward_cfg, *succ) {
            if is_stop_block(ctx, succ_upper) {
                return true;
            }
        }
    }

    false
}

/// Check if any successor block leads to a Stop block
fn successors_have_stop_block(ctx: &DiscoveryContext, block: BlockId, stop: BlockId) -> bool {
    let mut visited = BTreeSet::new();
    let mut worklist = vec![block];

    while let Some(current) = worklist.pop() {
        if current == stop || !visited.insert(current) {
            continue;
        }

        if let Some((_, upper)) = block_bounds(&ctx.forward_cfg, current) {
            if is_stop_block(ctx, upper) {
                return true;
            }
        }

        // Only check immediate successors, not full reachability
        for succ in ctx.forward_cfg.successors(current) {
            if visited.len() < 10 {  // Limit exploration depth
                worklist.push(*succ);
            }
        }
    }

    false
}

/// Discover the body of a loop, stopping when we hit a Stop block or return to the header
fn discover_loop_body(ctx: &mut DiscoveryContext, start: BlockId, stop: BlockId) -> IRNode {
    let mut node = IRNode::default();
    let mut cursor = start;

    while cursor != stop {
        let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, cursor) else {
            cursor = next_block(ctx, cursor, stop);
            continue;
        };

        // Stop when we hit an invariant check block (ends with Stop)
        if is_stop_block(ctx, upper) {
            break;
        }

        // Translate this block
        let block_ir = translate_range_skip_loop_artifacts(ctx, lower, upper);
        node = node.combine(block_ir);

        // Check if this block terminates
        if matches!(
            ctx.target.get_bytecode()[upper as usize],
            Bytecode::Ret(_, _) | Bytecode::Abort(_, _)
        ) {
            break;
        }

        // Handle branches within the loop body
        if let Bytecode::Branch(_, then_label, else_label, cond_temp) =
            ctx.target.get_bytecode()[upper as usize].clone()
        {
            let cond_name = ir_translator::temp_id(ctx, cond_temp);
            let then_block = resolve_label_block(ctx, then_label).expect("then label must resolve");
            let else_block = resolve_label_block(ctx, else_label).expect("else label must resolve");

            // Check if either branch leads to the Stop block (loop back)
            let then_is_stop = is_invariant_check_block(ctx, then_block) ||
                               successors_have_stop_block(ctx, then_block, stop);
            let else_is_stop = is_invariant_check_block(ctx, else_block) ||
                               successors_have_stop_block(ctx, else_block, stop);

            if then_is_stop && else_is_stop {
                // Both branches lead to loop back - we're done with body
                break;
            } else if then_is_stop {
                // Then leads to loop back, else continues
                cursor = else_block;
                continue;
            } else if else_is_stop {
                // Else leads to loop back, then continues
                cursor = then_block;
                continue;
            } else {
                // Regular if-then-else within loop body
                let merge = find_merge_block(ctx, then_block, else_block, stop).unwrap_or(stop);
                let then_ir = discover_region(ctx, then_block, merge);
                let else_ir = discover_region(ctx, else_block, merge);

                node = node.combine(IRNode::If {
                    cond: Box::new(IRNode::Var(cond_name)),
                    then_branch: Box::new(then_ir),
                    else_branch: Box::new(else_ir),
                });

                cursor = merge;
                continue;
            }
        }

        cursor = next_block(ctx, cursor, stop);
    }

    node
}


fn next_block(ctx: &DiscoveryContext, current: BlockId, stop: BlockId) -> BlockId {
    *ctx.forward_cfg.successors(current).first().unwrap_or(&stop)
}

/// Check if a block ends with a Stop operation (loop invariant checking block)
fn is_stop_block(ctx: &DiscoveryContext, upper: CodeOffset) -> bool {
    matches!(
        ctx.target.get_bytecode().get(upper as usize),
        Some(Bytecode::Call(_, _, move_stackless_bytecode::stackless_bytecode::Operation::Stop, _, _))
    )
}

/// Check if a block is a loop invariant checking block (ends with Stop)
fn is_invariant_check_block(ctx: &DiscoveryContext, block: BlockId) -> bool {
    if let Some((_, upper)) = block_bounds(&ctx.forward_cfg, block) {
        is_stop_block(ctx, upper)
    } else {
        false
    }
}

/// Check if target is reachable from source (without going through stop)
fn reaches(
    cfg: &move_stackless_bytecode::stackless_control_flow_graph::StacklessControlFlowGraph,
    source: BlockId,
    target: BlockId,
    stop: BlockId,
) -> bool {
    let mut visited = BTreeSet::new();
    let mut worklist = vec![source];

    while let Some(block) = worklist.pop() {
        if block == stop || !visited.insert(block) {
            continue;
        }
        if block == target {
            return true;
        }
        worklist.extend(cfg.successors(block));
    }

    false
}

fn find_merge_block(
    ctx: &DiscoveryContext,
    then_block: BlockId,
    else_block: BlockId,
    stop: BlockId,
) -> Option<BlockId> {
    use move_stackless_bytecode::stackless_bytecode::Bytecode;

    // Helper to check if a block terminates (returns or aborts)
    let block_terminates = |block: BlockId| -> bool {
        if let Some((start, end)) = block_bounds(&ctx.forward_cfg, block) {
            let code = ctx.target.get_bytecode();
            for offset in start..=end {
                if let Some(bytecode) = code.get(offset as usize) {
                    if matches!(bytecode, Bytecode::Ret(_, _) | Bytecode::Abort(_, _)) {
                        return true;
                    }
                }
            }
        }
        false
    };

    let cfg = &ctx.forward_cfg;
    let mut then_reachable = BTreeSet::new();
    let mut worklist = vec![then_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !then_reachable.insert(block) {
            continue;
        }
        // Don't explore successors if this block terminates
        if !block_terminates(block) {
            worklist.extend(cfg.successors(block));
        }
    }

    let mut else_reachable = BTreeSet::new();
    let mut worklist = vec![else_block];
    while let Some(block) = worklist.pop() {
        if block == stop || !else_reachable.insert(block) {
            continue;
        }
        // Don't explore successors if this block terminates
        if !block_terminates(block) {
            worklist.extend(cfg.successors(block));
        }
    }

    then_reachable.intersection(&else_reachable).copied().min()
}

/// Find the label bytecode in a block.
/// If multiple labels exist, prefer the one that is a loop header.
fn find_label_in_block(ctx: &DiscoveryContext, block: BlockId) -> Option<Label> {
    let Some((lower, upper)) = block_bounds(&ctx.forward_cfg, block) else {
        return None;
    };

    let code = ctx.target.get_bytecode();
    let loop_annotation = ctx.target.get_annotations().get::<LoopAnnotation>();

    let mut first_label = None;

    for offset in lower..=upper {
        if let Bytecode::Label(_, label) = &code[offset as usize] {
            // Prefer loop header labels if LoopAnnotation is available
            if let Some(annotation) = &loop_annotation {
                if annotation.fat_loops.contains_key(label) {
                    return Some(*label);
                }
            }
            // Remember the first label as fallback
            if first_label.is_none() {
                first_label = Some(*label);
            }
        }
    }

    first_label
}

/// Extract loop invariants from the LoopAnnotation for a given loop header label.
/// Returns the invariant IR nodes.
fn extract_invariants_for_label(
    ctx: &mut DiscoveryContext,
    label: Label,
) -> Vec<IRNode> {
    // Try to get LoopAnnotation from function target
    let loop_annotation = ctx.target.get_annotations().get::<LoopAnnotation>();

    let Some(annotation) = loop_annotation else {
        return vec![];
    };

    let Some(fat_loop) = annotation.fat_loops.get(&label) else {
        return vec![];
    };

    let mut invariants = Vec::new();

    // The loop_invariant.code contains bytecodes that represent the invariant
    // These are typically ensures() calls. We need to translate them.
    for bytecode in &fat_loop.loop_invariant.code {
        // We can't use the normal translate function since these bytecodes
        // aren't part of the main code array at a specific offset.
        // Instead, extract the condition from Call operations to ensures()
        if let Bytecode::Call(_, _, op, args, _) = bytecode {
            // Check if this is an ensures() call
            if let move_stackless_bytecode::stackless_bytecode::Operation::Function(mod_id, fun_id, _) = op {
                let func_env = ctx.target.func_env.module_env.env.get_function(mod_id.qualified(*fun_id));
                if func_env.get_name_str() == "ensures" {
                    // The argument to ensures() is the condition
                    // It's a temp index that we need to look up
                    if let Some(&temp_idx) = args.first() {
                        let var_name = ir_translator::temp_id(ctx, temp_idx);
                        invariants.push(IRNode::Var(var_name));
                    }
                }
            }
        }
    }

    invariants
}

/// Get all loop invariant AttrIds for a function.
/// These are stored in TargetedLoopInfo.attrs as vectors of AttrIds.
fn get_loop_invariant_attrs(ctx: &DiscoveryContext) -> BTreeSet<AttrId> {
    ctx.target
        .get_annotations()
        .get::<TargetedLoopInfo>()
        .map(|info| info.attrs.iter().flatten().cloned().collect())
        .unwrap_or_default()
}

/// Translate a bytecode range, skipping loop analysis artifacts.
/// Returns the translated IR.
fn translate_range_skip_loop_artifacts(
    ctx: &mut DiscoveryContext,
    lower: CodeOffset,
    upper: CodeOffset,
) -> IRNode {
    let loop_invariant_attrs = get_loop_invariant_attrs(ctx);

    let mut result = IRNode::default();

    for offset in lower..=upper {
        let bytecode = &ctx.target.get_bytecode()[offset as usize];
        let attr_id = bytecode.get_attr_id();

        // Skip bytecodes that are part of loop invariants
        if loop_invariant_attrs.contains(&attr_id) {
            continue;
        }

        let node = ir_translator::translate(ctx, offset);
        let terminates = node.terminates();
        result = result.combine(node);
        if terminates {
            break;
        }
    }

    result
}

/// Translate constants and setup instructions from merge block
/// This ensures constant values are available before the while condition is evaluated
fn translate_constants_and_setup(
    ctx: &mut DiscoveryContext,
    lower: CodeOffset,
    upper: CodeOffset,
    cond_temp: usize,
) -> IRNode {
    // First pass: collect offsets to translate
    let offsets_to_translate: Vec<CodeOffset> = {
        let bytecodes = ctx.target.get_bytecode();
        (lower..upper)
            .filter(|&offset| {
                let bytecode = &bytecodes[offset as usize];
                // Translate Load instructions (constants)
                // Skip the instruction that defines cond_temp (handled separately)
                matches!(bytecode, Bytecode::Load(_, dest, _) if *dest != cond_temp)
            })
            .collect()
    };

    // Second pass: translate
    let mut result = IRNode::default();
    for offset in offsets_to_translate {
        let node = ir_translator::translate(ctx, offset);
        result = result.combine(node);
    }

    result
}

/// Find the expression that computes the loop condition
/// Looks for the instruction that defines `cond_temp` and extracts its RHS.
/// Also resolves variable copies (e.g., `let t_t22 := carry` -> use `carry` directly)
/// so that the condition refers to loop variables instead of stale copies.
fn find_condition_expression(
    ctx: &mut DiscoveryContext,
    lower: CodeOffset,
    upper: CodeOffset,
    cond_temp: usize,
) -> IRNode {
    let bytecodes = ctx.target.get_bytecode();

    // First pass: build a map of simple variable copies (Assign instructions)
    // e.g., `let t_t22 := carry` means t_t22 -> carry
    let mut var_copies: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    for offset in lower..upper {
        if let Bytecode::Assign(_, dest, src, _) = &bytecodes[offset as usize] {
            let dest_name = ir_translator::temp_id(ctx, *dest);
            let src_name = ir_translator::temp_id(ctx, *src);
            var_copies.insert(dest_name, src_name);
        }
    }

    // Search backwards from the branch to find the instruction that defines cond_temp
    for offset in (lower..upper).rev() {
        let bytecode = &bytecodes[offset as usize];

        // Check if this instruction defines cond_temp by checking specific bytecode types
        let defines_temp = match bytecode {
            Bytecode::Call(_, dests, _, _, _) => dests.contains(&cond_temp),
            Bytecode::Load(_, dest, _) => *dest == cond_temp,
            Bytecode::Assign(_, dest, _, _) => *dest == cond_temp,
            _ => false,
        };

        if defines_temp {
            // Found it - translate this instruction and extract the RHS
            let node = ir_translator::translate(ctx, offset);

            // If it's a Let { pattern, value }, extract the value
            let expr = if let IRNode::Let { value, .. } = node {
                *value
            } else {
                node
            };

            // Resolve variable copies in the expression
            // This replaces temps like t_t22 with their source (carry)
            return resolve_var_copies(expr, &var_copies);
        }
    }

    // Fallback: just use the variable
    IRNode::Var(ir_translator::temp_id(ctx, cond_temp))
}

/// Resolve variable copies in an expression.
/// Recursively replaces variables that are simple copies with their source.
fn resolve_var_copies(
    expr: IRNode,
    var_copies: &std::collections::BTreeMap<String, String>,
) -> IRNode {
    expr.map(&mut |node| {
        if let IRNode::Var(name) = &node {
            // Follow the chain of copies to find the original variable
            let mut current = name.clone();
            while let Some(source) = var_copies.get(&current) {
                current = source.clone();
            }
            if &current != name {
                return IRNode::Var(current);
            }
        }
        node
    })
}
