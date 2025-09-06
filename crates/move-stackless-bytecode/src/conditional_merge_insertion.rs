// Copyright (c) Asymptotic
// SPDX-License-Identifier: Apache-2.0

//! Conditional Merge Insertion Pass
//!
//! This pass implements a principled approach to conditional merge insertion that converts
//! simple if-then-else bytecode into explicit if-then-else calls. This is a simplified
//! partial SSA conversion focused only on non-nested conditional blocks.
//!
//! ## Algorithm
//!
//! The implementation is based on standard dataflow analyses:
//! 1. **Def-Use Analysis** - Find variables defined in branches and used after merge point
//! 2. **Live Variable Analysis** - Only create ite expressions for live variables (pruned SSA)
//! 3. **Reaching Definitions** - Identify variables with multiple reaching definitions at merge points
//!
//! ## Scope Limitations
//! - Only if-then-else blocks (no loops)
//! - No nesting (single level conditionals only)
//! - No early returns/aborts

use std::collections::BTreeSet;

use move_binary_format::file_format::CodeOffset;
use move_model::{
    model::FunctionEnv,
    ty::{PrimitiveType, Type},
};


use crate::{
    ast::TempIndex,
    function_target::{FunctionData, FunctionTarget},
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    graph::{DomRelation, Graph},
    livevar_analysis::LiveVarAnnotation,
    reaching_def_analysis::{Def, ReachingDefAnnotation},
    stackless_bytecode::{AttrId, Bytecode, Operation},
    stackless_control_flow_graph::{BlockContent, BlockId, StacklessControlFlowGraph},
};

pub struct ConditionalMergeInsertionProcessor {
    debug: bool,
}

impl ConditionalMergeInsertionProcessor {
    pub fn new() -> Box<Self> {
        Box::new(Self { debug: false })
    }

    pub fn new_with_debug() -> Box<Self> {
        Box::new(Self { debug: true })
    }

    /// Find simple if-then-else structures only
    fn find_simple_conditionals(
        &self,
        target: &FunctionTarget,
        cfg: &StacklessControlFlowGraph,
    ) -> Vec<ConditionalStructure> {
        let mut conditionals = Vec::new();

        for node in cfg.blocks() {
            if let Some(conditional_jump) = self.extract_conditional_jump(cfg, node, target) {
                // Must be simple if-then-else: exactly 2 successors
                let successors = cfg.successors(node);
                if successors.len() == 2 {
                    let true_branch = successors[0];
                    let false_branch = successors[1];

                    // Find merge point - should be unique immediate post-dominator
                    if let Some(merge_point) = self.find_immediate_post_dominator(node, cfg, target) {
                        // Check for if-then-else structure
                        if self.is_simple_structure(
                            node,
                            true_branch,
                            false_branch,
                            merge_point,
                            cfg,
                        ) {
                            conditionals.push(ConditionalStructure {
                                condition_var: conditional_jump.condition,
                                true_branch,
                                false_branch,
                                merge_point,
                                is_if_then: false,
                            });
                        }
                        // Check for if-then structure (one branch goes directly to merge)
                        else if self.is_simple_if_then_structure(
                            node,
                            true_branch,
                            false_branch,
                            merge_point,
                            cfg,
                        ) {
                            conditionals.push(ConditionalStructure {
                                condition_var: conditional_jump.condition,
                                true_branch,
                                false_branch,
                                merge_point,
                                is_if_then: true,
                            });
                        }
                    }
                }
            }
        }

        if self.debug {
            println!("Found {} simple conditionals", conditionals.len());
        }

        conditionals
    }

    /// Extract conditional jump information from a block
    fn extract_conditional_jump(
        &self,
        cfg: &StacklessControlFlowGraph,
        node: BlockId,
        target: &FunctionTarget,
    ) -> Option<ConditionalJump> {
        if let Some(range) = cfg.instr_indexes(node) {
            // Look for the conditional branch instruction in this block
            for pc in range {
                if let Some(bytecode) = target.data.code.get(pc as usize) {
                    match bytecode {
                        Bytecode::Branch(_, _, _, temp) => {
                            // Found conditional branch - extract condition variable
                            let successors = cfg.successors(node);
                            if successors.len() == 2 {
                                return Some(ConditionalJump {
                                    condition: *temp,
                                });
                            }
                        }
                        _ => continue,
                    }
                }
            }
        }
        None
    }

    /// Check if this represents a simple if-then-else structure
    fn is_simple_structure(
        &self,
        _condition: BlockId,
        true_branch: BlockId,
        false_branch: BlockId,
        merge: BlockId,
        cfg: &StacklessControlFlowGraph,
    ) -> bool {
        // True branch must go directly to merge (no internal branching)
        let true_successors = cfg.successors(true_branch);
        let false_successors = cfg.successors(false_branch);

        true_successors.len() == 1
            && true_successors[0] == merge
            && false_successors.len() == 1
            && false_successors[0] == merge
    }

    /// Check if this represents a simple if-then structure (one branch goes directly to merge)
    fn is_simple_if_then_structure(
        &self,
        _condition: BlockId,
        true_branch: BlockId,
        false_branch: BlockId,
        merge: BlockId,
        cfg: &StacklessControlFlowGraph,
    ) -> bool {
        let true_successors = cfg.successors(true_branch);
        let false_successors = cfg.successors(false_branch);

        // Pattern 1: true branch goes to merge, false branch is the merge (fallthrough)
        if false_branch == merge && true_successors.len() == 1 && true_successors[0] == merge {
            if self.debug {
                println!("Found if-then pattern: true_branch {} -> merge {}, false_branch {} == merge", 
                    true_branch, merge, false_branch);
            }
            return true;
        }

        // Pattern 2: false branch goes to merge, true branch is the merge (fallthrough)
        if true_branch == merge && false_successors.len() == 1 && false_successors[0] == merge {
            if self.debug {
                println!("Found if-then pattern: false_branch {} -> merge {}, true_branch {} == merge", 
                    false_branch, merge, true_branch);
            }
            return true;
        }

        false
    }

    /// Find the immediate post-dominator (merge point) for conditional branches  
    fn find_immediate_post_dominator(
        &self,
        condition_node: BlockId,
        cfg: &StacklessControlFlowGraph,
        target: &FunctionTarget,
    ) -> Option<BlockId> {
        let successors = cfg.successors(condition_node);
        if successors.len() != 2 {
            return None;
        }

        let true_branch = successors[0];
        let false_branch = successors[1];

        // Use dominator analysis approach from reference implementation
        let entry = cfg.entry_block();
        let nodes = cfg.blocks();
        let edges: Vec<(BlockId, BlockId)> = nodes
            .iter()
            .flat_map(|x| {
                cfg.successors(*x)
                    .iter()
                    .map(|y| (*x, *y))
                    .collect::<Vec<(BlockId, BlockId)>>()
            })
            .collect();
        let graph = Graph::new(entry, nodes.clone(), edges);
        let dom_relation = DomRelation::new(&graph);

        // Find all reachable blocks that could be merge points
        let reachable_blocks: Vec<_> = nodes
            .into_iter()
            .filter(|&block| dom_relation.is_reachable(block))
            .collect();

        // The merge point should be a block that is reachable from both
        // branches and is the closest common post-dominator
        for &candidate in &reachable_blocks {
            // Check if this candidate can be reached from both branches
            if self.can_reach_block(cfg, true_branch, candidate)
                && self.can_reach_block(cfg, false_branch, candidate)
            {
                if self.debug {
                    println!("Found potential merge point: block {} (reachable from both branches)", candidate);
                    // Debug all blocks on first candidate
                    if candidate == 1 {
                        println!("All blocks in CFG:");
                        let mut all_blocks: Vec<_> = cfg.blocks().into_iter().collect();
                        all_blocks.sort();
                        for block in all_blocks {
                            if let Some(range) = cfg.instr_indexes(block) {
                                let range_vec: Vec<CodeOffset> = range.collect();
                                println!("  Block {}: PCs {:?}", block, range_vec);
                            } else {
                                println!("  Block {}: No instruction range (dummy)", block);
                            }
                        }
                        println!("True branch: {}, False branch: {}", true_branch, false_branch);
                    }
                }
                // This is a potential merge point - verify it's the immediate
                // post-dominator by checking no other valid merge point
                // dominates this one
                let mut is_immediate = true;
                for &other in &reachable_blocks {
                    if other != candidate
                        && self.can_reach_block(cfg, true_branch, other)
                        && self.can_reach_block(cfg, false_branch, other)
                        && dom_relation.is_dominated_by(candidate, other)
                    {
                        if self.debug {
                            println!("Block {} is dominated by {}, not immediate", candidate, other);
                        }
                        is_immediate = false;
                        break;
                    }
                }
                if is_immediate {
                    if self.debug {
                        println!("Selected merge point: block {}", candidate);
                        // Debug: show what PC this block maps to
                        let cfg_for_pc = StacklessControlFlowGraph::new_forward(&target.data.code);
                        if let Some(range) = cfg_for_pc.instr_indexes(candidate) {
                            let range_vec: Vec<CodeOffset> = range.collect();
                            println!("Block {} contains PCs: {:?}", candidate, range_vec);
                        }
                    }
                    return Some(candidate);
                }
            }
        }

        None
    }



    /// Check if we can reach target_block from start_block
    fn can_reach_block(
        &self,
        cfg: &StacklessControlFlowGraph,
        start_block: BlockId,
        target_block: BlockId,
    ) -> bool {
        if start_block == target_block {
            return true;
        }

        let mut visited = BTreeSet::new();
        let mut queue = vec![start_block];
        visited.insert(start_block);

        while let Some(current) = queue.pop() {
            for &successor in cfg.successors(current) {
                if successor == target_block {
                    return true;
                }
                if !visited.contains(&successor) {
                    visited.insert(successor);
                    queue.push(successor);
                }
            }
        }

        false
    }

    /// Apply the main dataflow analysis algorithm
    fn process_conditional(
        &self,
        conditional: &ConditionalStructure,
        target: &FunctionTarget,
        live_vars: &LiveVarAnnotation,
        reaching_defs: &ReachingDefAnnotation,
    ) -> Vec<VariableToMerge> {
        let mut variables_to_merge = Vec::new();

        // Step 1: Get live variables at merge point  
        let merge_pc = self.get_block_start_pc(target, conditional.merge_point);
        
        // Use detected merge point for liveness, but look for actual convergence point for reaching defs
        let live_at_merge = if let Some(pc) = merge_pc {
            live_vars
                .get_live_var_info_at(pc)
                .map(|info| info.before.clone())
                .unwrap_or_default()
        } else {
            BTreeSet::new()
        };
        
        // Find the convergence point - where multiple reaching definitions meet
        let convergence_pc = self.find_convergence_point_for_conditional(
            target, 
            conditional, 
            merge_pc,
            reaching_defs
        );

        if self.debug {
            println!("Merge point PC: {:?} -> Convergence: {:?}", merge_pc, convergence_pc);
            println!("Live variables at merge point: {:?}", live_at_merge);
            
            // Debug: Check liveness at both PCs
            if let Some(pc) = merge_pc {
                if let Some(live_info) = live_vars.get_live_var_info_at(pc) {
                    println!("Live variables at original PC {}: {:?}", pc, live_info.before);
                }
            }
            if let Some(pc) = convergence_pc {
                if let Some(live_info) = live_vars.get_live_var_info_at(pc) {
                    println!("Live variables at convergence PC {}: {:?}", pc, live_info.before);
                }
                if let Some(reaching_state) = reaching_defs.get_reaching_def_info_at(pc) {
                    println!("Reaching definitions state at PC {}: {:?}", pc, reaching_state);
                }
            }
        }

        // Step 2: For each live variable, check reaching definitions
        for &var in &live_at_merge {
            if let Some(pc) = convergence_pc {
                if let Some(reaching_state) = reaching_defs.get_reaching_def_info_at(pc) {
                    if let Some(reaching_defs_set) = reaching_state.map.get(&var) {
                        // Step 3: If multiple definitions reach here, need ite
                        if reaching_defs_set.len() > 1 {
                            if self.debug {
                                println!("Variable {} has {} reaching definitions: {:?}", var, reaching_defs_set.len(), reaching_defs_set);
                            }
                            
                            // Extract the actual assignment values from reaching definitions
                            let (true_value, false_value) = self.extract_branch_values_from_reaching_defs(
                                reaching_defs_set,
                                conditional,
                                target,
                            );
                            
                            if self.debug {
                                println!("Branch values - True: {:?}, False: {:?}", true_value, false_value);
                            }

                            if let (Some(tv), Some(fv)) = (true_value, false_value) {
                                variables_to_merge.push(VariableToMerge {
                                    variable: var,
                                    condition: conditional.condition_var,
                                    true_value: tv,
                                    false_value: fv,
                                    merge_point: conditional.merge_point,
                                });
                            }
                        }
                    }
                }
            }
        }

        if self.debug {
            println!("Variables to merge: {:?}", variables_to_merge);
        }

        variables_to_merge
    }

    /// Find the convergence point deterministically using the merge point from dominator analysis
    fn find_convergence_point_for_conditional(
        &self,
        target: &FunctionTarget,
        conditional: &ConditionalStructure,
        merge_pc: Option<CodeOffset>,
        reaching_defs: &ReachingDefAnnotation,
    ) -> Option<CodeOffset> {
        // The convergence point should be at the merge point determined by dominator analysis
        // We just need to find the exact PC within that block where reaching definitions converge
        
        if let Some(base_pc) = merge_pc {
            let cfg = StacklessControlFlowGraph::new_forward(&target.data.code);
            
            // Get all PCs in the merge block
            if let Some(range) = cfg.instr_indexes(conditional.merge_point) {
                for pc in range {
                    if let Some(reaching_state) = reaching_defs.get_reaching_def_info_at(pc) {
                        // Check if any variable has multiple reaching definitions from different branches
                        for (var, defs) in &reaching_state.map {
                            if defs.len() > 1 {
                                // Verify these definitions come from different branches
                                let def_blocks: BTreeSet<BlockId> = defs
                                    .iter()
                                    .filter_map(|def| match def {
                                        Def::Alias(_, offset) => self.pc_to_block(&cfg, *offset),
                                    })
                                    .collect();
                                
                                // Check if we have definitions from both branches
                                let has_true_branch = def_blocks.contains(&conditional.true_branch) ||
                                    def_blocks.iter().any(|&block| self.can_reach_block(&cfg, conditional.true_branch, block));
                                let has_false_branch = def_blocks.contains(&conditional.false_branch) ||
                                    def_blocks.iter().any(|&block| self.can_reach_block(&cfg, conditional.false_branch, block));
                                
                                if has_true_branch && has_false_branch {
                                    if self.debug {
                                        println!("Found deterministic convergence point at PC {} for variable {} with {} definitions", pc, var, defs.len());
                                    }
                                    return Some(pc);
                                }
                            }
                        }
                    }
                }
            }
            
            // If no convergence found in merge block, return the start of merge block
            Some(base_pc)
        } else {
            None
        }
    }

    /// Extract the actual values assigned in each branch from reaching definitions
    fn extract_branch_values_from_reaching_defs(
        &self,
        reaching_defs_set: &BTreeSet<Def>,
        conditional: &ConditionalStructure,
        target: &FunctionTarget,
    ) -> (Option<TempIndex>, Option<TempIndex>) {
        let cfg = StacklessControlFlowGraph::new_forward(&target.data.code);
        let mut true_value = None;
        let mut false_value = None;
        let mut fallthrough_value = None;
        
        for def in reaching_defs_set {
            let Def::Alias(temp_var, def_pc) = def;
            if let Some(block) = self.pc_to_block(&cfg, *def_pc) {
                if self.debug {
                    println!("Analyzing def at PC {} in block {} -> temp {}", def_pc, block, temp_var);
                }
                
                // Get the actual value being assigned at this PC
                if let Some(assigned_value) = self.get_assigned_variable_at_pc(target, *def_pc) {
                    // Determine which branch this definition comes from
                    if block == conditional.true_branch {
                        true_value = Some(assigned_value);
                        if self.debug {
                            println!("True branch value: temp {}", assigned_value);
                        }
                    } else if block == conditional.false_branch && !conditional.is_if_then {
                        false_value = Some(assigned_value);
                        if self.debug {
                            println!("False branch value: temp {}", assigned_value);
                        }
                    } else {
                        // Check if this block is reachable from one specific branch
                        let reachable_from_true = self.can_reach_block(&cfg, conditional.true_branch, block);
                        let reachable_from_false = self.can_reach_block(&cfg, conditional.false_branch, block);
                        
                        if reachable_from_true && !reachable_from_false {
                            true_value = Some(assigned_value);
                            if self.debug {
                                println!("True branch value (via reachability): temp {}", assigned_value);
                            }
                        } else if !reachable_from_true && reachable_from_false && !conditional.is_if_then {
                            false_value = Some(assigned_value);
                            if self.debug {
                                println!("False branch value (via reachability): temp {}", assigned_value);
                            }
                        } else if !reachable_from_true && !reachable_from_false {
                            // This is likely a pre-conditional definition (fallthrough value)
                            fallthrough_value = Some(assigned_value);
                            if self.debug {
                                println!("Fallthrough value: temp {}", assigned_value);
                            }
                        } else if self.debug {
                            println!("Ambiguous branch membership for PC {} in block {} (true: {}, false: {})", def_pc, block, reachable_from_true, reachable_from_false);
                        }
                    }
                }
            }
        }
        
        // Handle fallthrough cases for both if-then and if-then-else patterns
        if let Some(fallthrough) = fallthrough_value {
            if conditional.is_if_then {
                if conditional.false_branch == conditional.merge_point {
                    // False branch is fallthrough, true branch has assignment
                    false_value = Some(fallthrough);
                    if self.debug {
                        println!("If-then: false branch (fallthrough) = temp {}", fallthrough);
                    }
                } else if conditional.true_branch == conditional.merge_point {
                    // True branch is fallthrough, false branch has assignment
                    true_value = Some(fallthrough);
                    if self.debug {
                        println!("If-then: true branch (fallthrough) = temp {}", fallthrough);
                    }
                }
            } else {
                // For if-then-else, use fallthrough for whichever branch doesn't have a value
                if true_value.is_none() {
                    true_value = Some(fallthrough);
                    if self.debug {
                        println!("If-then-else: true branch uses fallthrough = temp {}", fallthrough);
                    }
                }
                if false_value.is_none() {
                    false_value = Some(fallthrough);
                    if self.debug {
                        println!("If-then-else: false branch uses fallthrough = temp {}", fallthrough);
                    }
                }
            }
        }
        
        (true_value, false_value)
    }




    /// Get the variable assigned at a particular PC
    fn get_assigned_variable_at_pc(
        &self,
        target: &FunctionTarget,
        pc: CodeOffset,
    ) -> Option<TempIndex> {
        if let Some(bytecode) = target.data.code.get(pc as usize) {
            if self.debug {
                println!("Examining bytecode at PC {}: {:?}", pc, bytecode);
            }
            match bytecode {
                Bytecode::Assign(_, _dest, src, _) => Some(*src), // Return the source of assignment
                Bytecode::Call(_, _dests, _, srcs, _) => {
                    // For calls, we could return the first source if available
                    srcs.first().copied()
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Get the starting PC of a block
    fn get_block_start_pc(&self, target: &FunctionTarget, block_id: BlockId) -> Option<CodeOffset> {
        let cfg = StacklessControlFlowGraph::new_forward(&target.data.code);
        match cfg.content(block_id) {
            BlockContent::Basic { lower, .. } => Some(*lower),
            BlockContent::Dummy => None,
        }
    }

    /// Find which block contains a given PC
    fn pc_to_block(&self, cfg: &StacklessControlFlowGraph, pc: CodeOffset) -> Option<BlockId> {
        for block_id in cfg.blocks() {
            if let Some(range) = cfg.instr_indexes(block_id) {
                let range_vec: Vec<CodeOffset> = range.collect();
                if range_vec.contains(&pc) {
                    return Some(block_id);
                }
            }
        }
        None
    }

    /// Insert if-then-else conditionals at merge points
    fn insert_conditionals(
        &self,
        variables_to_merge: Vec<VariableToMerge>,
        data: &mut FunctionData,
    ) {
        let mut next_temp = data.local_types.len();

        for var_info in variables_to_merge {
            if self.debug {
                println!("Processing variable {} for insertion", var_info.variable);
            }
            
            // Create new temporary for merged result
            let merged_temp = next_temp;
            next_temp += 1;

            // Add type for the new temporary (copy from original variable)
            if var_info.variable < data.local_types.len() {
                data.local_types
                    .push(data.local_types[var_info.variable].clone());
            } else {
                data.local_types.push(Type::Primitive(PrimitiveType::U64)); // fallback
            }

            // Create ite call
            let ite_call = Bytecode::Call(
                AttrId::new(0), // TODO: use appropriate attribute
                vec![merged_temp],
                Operation::IfThenElse,
                vec![
                    var_info.condition,
                    var_info.true_value,
                    var_info.false_value,
                ],
                None,
            );

            if self.debug {
                println!("Created IfThenElse call: temp{} = if_then_else(temp{}, temp{}, temp{})", 
                    merged_temp, var_info.condition, var_info.true_value, var_info.false_value);
            }

            // Insert at appropriate position relative to merge point
            if let Some(merge_pc) = self.get_merge_point_pc(data, var_info.merge_point) {
                if self.debug {
                    println!("Inserting IfThenElse at merge point PC {}", merge_pc);
                }
                
                // Determine where the if_then_else will actually be inserted
                let actual_insertion_point = if let Some(bytecode) = data.code.get(merge_pc as usize) {
                    match bytecode {
                        Bytecode::Label(_, _) => merge_pc + 1, // After label
                        _ => merge_pc, // At merge point
                    }
                } else {
                    merge_pc
                };
                
                self.insert_instruction_before_pc(&mut data.code, merge_pc, ite_call);

                // Replace uses of original variable with merged version after the inserted if_then_else
                // NOTE: After insertion, all subsequent PCs shift by 1, so we want to start 
                // replacement after the newly inserted instruction
                self.replace_variable_uses_after_point(
                    &mut data.code,
                    var_info.variable,
                    merged_temp,
                    actual_insertion_point + 1, // Start after the inserted if_then_else
                );
                
                if self.debug {
                    println!("Successfully inserted conditional for variable {}", var_info.variable);
                }
            } else {
                if self.debug {
                    println!("ERROR: Could not get merge point PC for block {}", var_info.merge_point);
                }
            }
        }
    }

    /// Get the PC for a merge point block
    fn get_merge_point_pc(&self, data: &FunctionData, merge_point: BlockId) -> Option<CodeOffset> {
        let cfg = StacklessControlFlowGraph::new_forward(&data.code);
        match cfg.content(merge_point) {
            BlockContent::Basic { lower, .. } => Some(*lower),
            BlockContent::Dummy => None,
        }
    }

    /// Insert an instruction at the appropriate position relative to a PC,
    /// handling labels at merge points correctly
    fn insert_instruction_before_pc(
        &self,
        code: &mut Vec<Bytecode>,
        pc: CodeOffset,
        instruction: Bytecode,
    ) {
        if pc as usize <= code.len() {
            let mut insertion_point = pc as usize;
            
            // If there's a label at the PC, insert after the label
            if let Some(bytecode) = code.get(pc as usize) {
                match bytecode {
                    Bytecode::Label(_, _) => {
                        insertion_point = pc as usize + 1;
                        if self.debug {
                            println!("Found label at PC {}, inserting if_then_else after it at position {}", pc, insertion_point);
                        }
                    }
                    _ => {
                        if self.debug {
                            println!("No label at PC {}, inserting if_then_else at position {}", pc, insertion_point);
                        }
                    }
                }
            }
            
            code.insert(insertion_point, instruction);
        }
    }

    /// Replace variable uses after a certain point using proper propagation
    fn replace_variable_uses_after_point(
        &self,
        code: &mut Vec<Bytecode>,
        old_var: TempIndex,
        new_var: TempIndex,
        after_pc: CodeOffset,
    ) {
        // Step 1: Scan all instructions AFTER the merge point
        for (pc, bytecode) in code.iter_mut().enumerate().skip(after_pc as usize) {
            // Step 2: Replace uses of original_var with new_var in this instruction
            let old_bytecode = bytecode.clone();
            *bytecode = self.replace_variable_in_bytecode(bytecode, old_var, new_var);
            
            if self.debug && !std::ptr::eq(&old_bytecode, bytecode) {
                println!("Replaced variable {} with {} at PC {}: {:?} -> {:?}", 
                    old_var, new_var, pc, old_bytecode, bytecode);
            }
            
            // Step 3: STOP if we encounter a new assignment to original_var
            // (This handles the case where the variable gets reassigned later)
            if self.instruction_assigns_to_variable(bytecode, old_var) {
                if self.debug {
                    println!("Stopping propagation at PC {} due to reassignment to {}", pc, old_var);
                }
                break;
            }
        }
    }

    /// Check if an instruction assigns to a specific variable
    fn instruction_assigns_to_variable(&self, bytecode: &Bytecode, var: TempIndex) -> bool {
        match bytecode {
            Bytecode::Assign(_, dest, _, _) => *dest == var,
            Bytecode::Call(_, dests, _, _, _) => dests.contains(&var),
            _ => false,
        }
    }

    /// Replace variable uses in a single bytecode instruction
    fn replace_variable_in_bytecode(
        &self,
        bytecode: &Bytecode,
        old_var: TempIndex,
        new_var: TempIndex,
    ) -> Bytecode {
        match bytecode {
            Bytecode::Assign(attr, dest, src, kind) => {
                let new_src = if *src == old_var { new_var } else { *src };
                Bytecode::Assign(attr.clone(), *dest, new_src, *kind)
            }
            Bytecode::Call(attr, dests, op, srcs, abort) => {
                let new_srcs: Vec<TempIndex> = srcs
                    .iter()
                    .map(|&src| if src == old_var { new_var } else { src })
                    .collect();
                Bytecode::Call(
                    attr.clone(),
                    dests.clone(),
                    op.clone(),
                    new_srcs,
                    abort.clone(),
                )
            }
            Bytecode::Ret(attr, srcs) => {
                // Replace uses in return values - CRITICAL for proper propagation
                let new_srcs: Vec<TempIndex> = srcs
                    .iter()
                    .map(|&src| if src == old_var { new_var } else { src })
                    .collect();
                Bytecode::Ret(attr.clone(), new_srcs)
            }
            Bytecode::Branch(attr, true_label, false_label, src) => {
                // Replace uses in branch conditions
                let new_src = if *src == old_var { new_var } else { *src };
                Bytecode::Branch(attr.clone(), *true_label, *false_label, new_src)
            }
            Bytecode::Jump(attr, label) => {
                Bytecode::Jump(attr.clone(), *label)
            }
            Bytecode::Label(attr, label) => {
                Bytecode::Label(attr.clone(), *label)
            }
            // For instructions that don't use variables, just clone
            _ => bytecode.clone(),
        }
    }
}

/// Conditional structure representing a simple if-then-else or if-then
#[derive(Debug, Clone)]
struct ConditionalStructure {
    condition_var: TempIndex,
    true_branch: BlockId,
    false_branch: BlockId, // For if-then, this might be the merge point (fallthrough)
    merge_point: BlockId,
    is_if_then: bool, // true for if-then, false for if-then-else
}

/// Variable that needs merging at a join point
#[derive(Debug, Clone)]
struct VariableToMerge {
    variable: TempIndex,
    condition: TempIndex,
    true_value: TempIndex,
    false_value: TempIndex,
    merge_point: BlockId,
}

/// Conditional jump information
#[derive(Debug, Clone)]
struct ConditionalJump {
    condition: TempIndex,
}

impl FunctionTargetProcessor for ConditionalMergeInsertionProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        mut data: FunctionData,
        _scc_opt: Option<&[FunctionEnv]>,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }

        if self.debug {
            println!(
                "Processing function {} for conditional merge insertion",
                func_env.get_full_name_str()
            );
        }

        // Build CFG
        let cfg = StacklessControlFlowGraph::new_forward(&data.code);
        let target = FunctionTarget::new(func_env, &data);

        // Find simple if-then-else structures only
        let conditionals = self.find_simple_conditionals(&target, &cfg);

        // Skip if no simple conditionals found
        if conditionals.is_empty() {
            if self.debug {
                println!("No simple conditionals found");
            }
            return data;
        }

        // Create target for analysis
        let target = FunctionTarget::new(func_env, &data);

        // Run required dataflow analyses
        // Note: We need the analyses to be run first, so this processor should come after them

        // Get live variable analysis results from current target
        let live_vars = data.annotations.get::<LiveVarAnnotation>();

        // Get reaching definitions analysis results from current target
        let reaching_defs = data.annotations.get::<ReachingDefAnnotation>();

        if self.debug {
            println!("Available annotations:");
            println!("  LiveVarAnnotation: {}", live_vars.is_some());
            println!("  ReachingDefAnnotation: {}", reaching_defs.is_some());
        }

        if let (Some(live_vars), Some(reaching_defs)) = (live_vars, reaching_defs) {
            // Apply main algorithm
            let mut all_variables_to_merge = Vec::new();
            for conditional in conditionals {
                let variables_to_merge =
                    self.process_conditional(&conditional, &target, &live_vars, &reaching_defs);
                all_variables_to_merge.extend(variables_to_merge);
            }

            if !all_variables_to_merge.is_empty() {
                if self.debug {
                    println!("About to insert {} conditionals", all_variables_to_merge.len());
                }
                self.insert_conditionals(all_variables_to_merge, &mut data);
            }
        } else {
            if self.debug {
                println!("Required dataflow analyses not available");
            }
        }

        if self.debug {
            println!(
                "Conditional merge insertion completed for {}",
                func_env.get_full_name_str()
            );
        }

        data
    }

    fn name(&self) -> String {
        "conditional_merge_insertion".to_string()
    }
}
