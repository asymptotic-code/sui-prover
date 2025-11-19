// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translates Move function bytecode to TheoremIR function bodies
//!
//! Single responsibility: Translate function bodies using BytecodeTranslator.
//! Populates SSA registry with type information from FunctionTarget.

use crate::data::{TheoremProgram, TheoremFunctionID};
use crate::data::types::{TempId, TheoremType};
use crate::data::statements::Statement;
use crate::data::expressions::Expression;
use crate::translation::bytecode_translator::BytecodeTranslator;
use move_model::model::{GlobalEnv, QualifiedId, FunId, DatatypeId};
use move_stackless_bytecode::function_target::FunctionTarget;
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant};
use move_stackless_bytecode::stackless_bytecode::Bytecode;
use move_stackless_bytecode::control_flow_reconstruction::{reconstruct_control_flow, StructuredBlock};
use std::collections::BTreeMap;
use crate::data::structure::TheoremStructID;

pub struct FunctionTranslator<'env> {
    env: &'env GlobalEnv,
    function_id_map: BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
    pub struct_id_map: BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
}

impl<'env> FunctionTranslator<'env> {
    pub fn new(
        env: &'env GlobalEnv,
        function_id_map: BTreeMap<QualifiedId<FunId>, TheoremFunctionID>,
        struct_id_map: BTreeMap<QualifiedId<DatatypeId>, TheoremStructID>,
    ) -> Self {
        Self {
            env,
            function_id_map,
            struct_id_map,
        }
    }

    /// Translate all function bodies in the program
    /// Only translates functions that are verification targets or their dependencies
    pub fn translate_all(
        &self,
        program: &mut TheoremProgram,
        targets: &FunctionTargetsHolder,
    ) {
        use std::collections::HashSet;

        // Identify functions to translate:
        // 1. Verified specs from target modules (like Boogie does)
        // 2. Their transitive dependencies

        let mut translated = HashSet::new();
        let mut to_process = Vec::new();

        // Collect verified spec functions from target modules
        for spec_id in targets.specs() {
            if let Some(&theorem_func_id) = self.function_id_map.get(spec_id) {
                let func_env = self.env.get_function(spec_id.clone());

                // Filter like Boogie: module must be target AND spec must be verified
                if func_env.module_env.is_target() && targets.is_verified_spec(spec_id) {
                    to_process.push(theorem_func_id);
                }
            }
        }

        // Iteratively translate functions and collect dependencies
        while let Some(func_id) = to_process.pop() {
            // Skip if already translated
            if translated.contains(&func_id) {
                continue;
            }

            // Translate this function
            self.translate_function_body(program, targets, func_id);
            translated.insert(func_id);

            // Extract dependencies from the translated body
            if let Some(func) = program.functions.get(&func_id) {
                let deps = self.extract_call_dependencies(&func.body);

                // Add dependencies to the processing queue
                for dep_id in deps {
                    if !translated.contains(&dep_id) {
                        to_process.push(dep_id);
                    }
                }
            }
        }
    }

    /// Extract function call dependencies from a statement
    fn extract_call_dependencies(&self, stmt: &Statement) -> Vec<TheoremFunctionID> {
        use crate::data::expressions::Expression;

        let mut deps = Vec::new();

        fn collect_from_expr(expr: &Expression, deps: &mut Vec<TheoremFunctionID>) {
            match expr {
                Expression::Call { function, args, .. } => {
                    deps.push(*function);
                    for arg in args {
                        collect_from_expr(arg, deps);
                    }
                }
                Expression::BinOp { lhs, rhs, .. } => {
                    collect_from_expr(lhs, deps);
                    collect_from_expr(rhs, deps);
                }
                Expression::UnOp { operand, .. } => {
                    collect_from_expr(operand, deps);
                }
                Expression::Cast { value, .. } => {
                    collect_from_expr(value, deps);
                }
                Expression::Pack { fields, .. } => {
                    for field in fields {
                        collect_from_expr(field, deps);
                    }
                }
                Expression::Unpack { operand, .. } | Expression::UnpackAll { operand, .. } => {
                    collect_from_expr(operand, deps);
                }
                Expression::VecOp { operands, .. } => {
                    for operand in operands {
                        collect_from_expr(operand, deps);
                    }
                }
                Expression::Temporary(_) | Expression::Constant(_) => {}
            }
        }

        fn collect_from_stmt(stmt: &Statement, deps: &mut Vec<TheoremFunctionID>) {
            match stmt {
                Statement::Let { operation, .. } => {
                    collect_from_expr(operation, deps);
                }
                Statement::Sequence(stmts) => {
                    for s in stmts {
                        collect_from_stmt(s, deps);
                    }
                }
                Statement::If { then_branch, else_branch, .. } => {
                    collect_from_stmt(then_branch, deps);
                    collect_from_stmt(else_branch, deps);
                }
                Statement::While { body, .. } => {
                    collect_from_stmt(body, deps);
                }
                Statement::Return { .. } | Statement::Abort { .. } |
                Statement::UpdateField { .. } | Statement::UpdateVectorElement { .. } |
                Statement::Requires { .. } | Statement::Ensures { .. } => {}
            }
        }

        collect_from_stmt(stmt, &mut deps);
        deps
    }

    /// Translate a single function body
    fn translate_function_body(
        &self,
        program: &mut TheoremProgram,
        targets: &FunctionTargetsHolder,
        func_id: TheoremFunctionID,
    ) {
        // Reverse-lookup: find the Move QualifiedId for this TheoremFunctionID
        let qualified_id = self.function_id_map
            .iter()
            .find(|(_, &id)| id == func_id)
            .map(|(qid, _)| qid.clone())
            .unwrap_or_else(|| {
                panic!("BUG: Function ID {} not found in function_id_map", func_id)
            });

        // Get the FunctionEnv from GlobalEnv
        let func_env = self.env.get_function(qualified_id);

        // Get the FunctionTarget from the pipeline
        let target = targets
            .get_target(&func_env, &FunctionVariant::Baseline);

        // Get the bytecode
        let code = target.get_bytecode();
        if code.is_empty() {
            // Native or abstract function - leave body empty
            return;
        }

        // Get mutable reference to function
        let func_mut = program
            .functions
            .get_mut(&func_id)
            .unwrap_or_else(|| {
                panic!("BUG: Function {} disappeared during translation", func_id)
            });

        // Populate SSA registry with types and set parameter names
        self.populate_types(&target, &mut func_mut.ssa_registry, &func_mut.signature.parameters);

        // Create bytecode translator
        let bytecode_translator = BytecodeTranslator::new(
            self.env,
            &self.function_id_map,
            &self.struct_id_map,
            &target,
        );

        // Use existing control flow reconstruction to get structured blocks
        // The reconstructor now computes phi-variables using formal dominance analysis,
        // so we don't need a separate phi computation pass
        let structured_blocks = reconstruct_control_flow(code);

        // Translate structured blocks to TheoremIR statements
        let body = self.translate_structured_blocks(
            &structured_blocks,
            &bytecode_translator,
            &mut func_mut.ssa_registry,
            code,
        );

        func_mut.body = body;
    }

    /// Extract phi variables with actual values from bytecode-level analysis.
    ///
    /// The phi_variables parameter already contains the correct then_value and else_value
    /// from bytecode-level scanning in phi_computation.rs. We just need to extract them.
    fn analyze_phi_pattern(
        &self,
        then_stmt: &Statement,
        else_stmt: &Statement,
        phi_variables: &[move_stackless_bytecode::control_flow_reconstruction::IfPhiVariable],
    ) -> Vec<crate::PhiVariable> {
        // First, process phi-variables from the reconstructor
        let mut result: Vec<crate::PhiVariable> = phi_variables.iter().filter_map(|phi_var| {
            let result_temp = phi_var.temp as TempId;
            let then_temp = phi_var.then_value as TempId;
            let else_temp = phi_var.else_value as TempId;

            // Try to extract the actual expression from the branch statements
            // If extraction fails, use a simple Temporary expression
            let then_expr = if then_temp == result_temp {
                // Placeholder - try to extract the actual expression
                self.extract_assigned_expression(then_stmt, result_temp)
                    .unwrap_or_else(|| Expression::Temporary(then_temp))
            } else {
                Expression::Temporary(then_temp)
            };

            let else_expr = if else_temp == result_temp {
                // Placeholder - try to extract the actual expression
                self.extract_assigned_expression(else_stmt, result_temp)
                    .unwrap_or_else(|| Expression::Temporary(else_temp))
            } else {
                Expression::Temporary(else_temp)
            };

            // Create phi-node if values differ or both are computed in branches
            let then_is_placeholder = then_temp == result_temp;
            let else_is_placeholder = else_temp == result_temp;

            // Only create phi if expressions differ OR both branches compute the value
            let should_create = !matches!((&then_expr, &else_expr), (Expression::Temporary(t1), Expression::Temporary(t2)) if t1 == t2)
                || (then_is_placeholder && else_is_placeholder);

            if should_create {
                Some(crate::PhiVariable {
                    result: result_temp,
                    then_value: then_expr,
                    else_value: else_expr,
                })
            } else {
                None
            }
        }).collect();

        // FALLBACK: Also check if both branches assign the same variable(s)
        // This handles cases where dominance analysis failed due to broken control flow (sorry/abort)
        let then_assigned = self.collect_assigned_variables(then_stmt);
        let else_assigned = self.collect_assigned_variables(else_stmt);

        // Find variables assigned in BOTH branches but not already in result
        let already_handled: std::collections::HashSet<_> = result.iter().map(|p| p.result).collect();

        for &var in then_assigned.iter() {
            if else_assigned.contains(&var) && !already_handled.contains(&var) {
                // Both branches assign this variable - create a phi-variable
                if let (Some(then_expr), Some(else_expr)) = (
                    self.extract_assigned_expression(then_stmt, var),
                    self.extract_assigned_expression(else_stmt, var)
                ) {
                    result.push(crate::PhiVariable {
                        result: var,
                        then_value: then_expr,
                        else_value: else_expr,
                    });
                }
            }
        }

        result
    }

    /// Collect all variables assigned in a statement
    fn collect_assigned_variables(&self, stmt: &Statement) -> std::collections::HashSet<TempId> {
        let mut vars = std::collections::HashSet::new();
        match stmt {
            Statement::Let { results, .. } => {
                vars.extend(results.iter().copied());
            }
            Statement::Sequence(stmts) => {
                for s in stmts {
                    vars.extend(self.collect_assigned_variables(s));
                }
            }
            Statement::If { then_branch, else_branch, .. } => {
                vars.extend(self.collect_assigned_variables(then_branch));
                vars.extend(self.collect_assigned_variables(else_branch));
            }
            _ => {}
        }
        vars
    }

    /// Extract the expression assigned to a variable in a statement.
    /// For example, in `let t5 ← call(...)`, this extracts the call expression.
    /// For `let t5 := t3`, this extracts Expression::Temporary(t3).
    fn extract_assigned_expression(&self, stmt: &Statement, target: TempId) -> Option<Expression> {
        match stmt {
            Statement::Let { results, operation, .. } => {
                // Check if this Let assigns to our target
                if results.contains(&target) {
                    // For single-result operations, return the operation itself
                    if results.len() == 1 && results[0] == target {
                        return Some(operation.clone());
                    }
                }
                None
            }
            Statement::Sequence(stmts) => {
                // Scan sequence to find assignment to target
                // Return the LAST assignment (SSA: last write wins)
                for stmt in stmts.iter().rev() {
                    if let Some(expr) = self.extract_assigned_expression(stmt, target) {
                        return Some(expr);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Translate StructuredBlocks from control flow reconstruction to TheoremIR statements
    fn translate_structured_blocks(
        &self,
        blocks: &[StructuredBlock],
        bytecode_translator: &BytecodeTranslator,
        registry: &mut crate::data::variables::VariableRegistry,
        code: &[Bytecode],
    ) -> Statement {
        let statements: Vec<Statement> = blocks
            .iter()
            .map(|block| self.translate_structured_block(block, bytecode_translator, registry, code))
            .collect();

        if statements.is_empty() {
            Statement::Sequence(vec![])
        } else if statements.len() == 1 {
            statements.into_iter().next().unwrap()
        } else {
            Statement::Sequence(statements)
        }
    }

    /// Translate a single StructuredBlock to TheoremIR Statement
    fn translate_structured_block(
        &self,
        block: &StructuredBlock,
        bytecode_translator: &BytecodeTranslator,
        registry: &mut crate::data::variables::VariableRegistry,
        code: &[Bytecode],
    ) -> Statement {
        match block {
            StructuredBlock::Basic { lower, upper } => {
                // Translate all bytecodes in this basic block
                let mut statements = Vec::new();

                for offset in *lower..=*upper {
                    let bytecode = &code[offset as usize];

                    // Skip branch/jump/label - they're handled by structured control flow
                    if matches!(bytecode, Bytecode::Branch(..) | Bytecode::Jump(..) | Bytecode::Label(..)) {
                        continue;
                    }

                    if let Some(stmt) = bytecode_translator.translate(bytecode, offset, registry) {
                        statements.push(stmt);
                    }
                }

                if statements.is_empty() {
                    Statement::Sequence(vec![])
                } else if statements.len() == 1 {
                    statements.into_iter().next().unwrap()
                } else {
                    Statement::Sequence(statements)
                }
            }

            StructuredBlock::Seq(blocks) => {
                let statements: Vec<Statement> = blocks
                    .iter()
                    .map(|b| self.translate_structured_block(b, bytecode_translator, registry, code))
                    .collect();

                if statements.is_empty() {
                    Statement::Sequence(vec![])
                } else if statements.len() == 1 {
                    statements.into_iter().next().unwrap()
                } else {
                    Statement::Sequence(statements)
                }
            }

            StructuredBlock::IfThenElse { cond_at: _, cond_temp, then_branch, else_branch, phi_variables } => {
                let then_stmt = self.translate_structured_block(then_branch, bytecode_translator, registry, code);
                let else_stmt = if let Some(else_block) = else_branch {
                    self.translate_structured_block(else_block, bytecode_translator, registry, code)
                } else {
                    Statement::Sequence(vec![])
                };

                // Analyze the translated statements to detect phi-merge pattern
                let phi_vars = self.analyze_phi_pattern(&then_stmt, &else_stmt, phi_variables);

                Statement::If {
                    condition: Expression::Temporary(*cond_temp as TempId),
                    then_branch: Box::new(then_stmt),
                    else_branch: Box::new(else_stmt),
                    phi_vars,
                }
            }

            StructuredBlock::While { cond_temp, condition_body, body, phi_variables, .. } => {
                // The condition_body contains the bytecode that computes the condition
                // The body contains the loop body (without the condition)
                let condition_stmt = self.translate_structured_block(condition_body, bytecode_translator, registry, code);
                let body_stmt = self.translate_structured_block(body, bytecode_translator, registry, code);

                // Convert phi variables to loop variables
                use crate::data::functions::LoopVariable;
                let loop_vars: Vec<LoopVariable> = phi_variables
                    .iter()
                    .filter_map(|phi| {
                        // Get type from registry - skip if not found
                        registry.get_type(phi.temp as TempId).cloned().map(|var_type| {
                            LoopVariable {
                                phi_result: phi.temp as TempId,
                                initial_value: phi.initial_value as TempId,
                                updated_value: phi.updated_value as TempId,
                                var_type,
                            }
                        })
                    })
                    .collect();

                Statement::While {
                    loop_vars,
                    condition: Expression::Temporary(*cond_temp as TempId),
                    body: Box::new(body_stmt),
                }
            }

            StructuredBlock::IfElseChain { branches, else_branch } => {
                // Convert chain to nested if-then-else
                let mut result: Option<Statement> = else_branch
                    .as_ref()
                    .map(|b| self.translate_structured_block(b, bytecode_translator, registry, code));

                // Build from the last branch backwards
                for ((_, cond_temp), branch_body) in branches.iter().rev() {
                    let then_stmt = self.translate_structured_block(branch_body, bytecode_translator, registry, code);
                    let else_stmt = result.unwrap_or_else(|| Statement::Sequence(vec![]));

                    result = Some(Statement::If {
                        condition: Expression::Temporary(*cond_temp as TempId),
                        then_branch: Box::new(then_stmt),
                        else_branch: Box::new(else_stmt),
                        phi_vars: vec![],  // IfElseChain doesn't have phi variables
                    });
                }

                result.unwrap_or_else(|| Statement::Sequence(vec![]))
            }
        }
    }

    /// Populate SSA registry with type information from FunctionTarget
    fn populate_types(
        &self,
        target: &FunctionTarget,
        registry: &mut crate::data::variables::VariableRegistry,
        parameters: &[crate::data::functions::Parameter],
    ) {
        let local_count = target.get_local_count();
        let param_count = target.get_parameter_count();

        for local_idx in 0..local_count {
            let temp_id = local_idx as TempId;
            let move_type = target.get_local_type(local_idx);
            let theorem_type = TheoremType::from_move_type(move_type, self.env, &self.struct_id_map);

            // Set type in registry
            registry.set_type(temp_id, theorem_type);

            // Get the name from FunctionTarget
            let symbol = target.get_local_name(local_idx);
            let compiler_name = symbol.display(self.env.symbol_pool()).to_string();

            // Set name: for parameters, use the human-readable name from the signature
            // For other locals, use the compiler-generated name from FunctionTarget
            if registry.get_name(temp_id).is_none() {
                let mut name = if local_idx < param_count {
                    // This is a parameter - use the human-readable name from signature
                    parameters.get(local_idx)
                        .map(|p| p.name.clone())
                        .unwrap_or_else(|| compiler_name.clone())
                } else {
                    // This is a local variable - use the compiler name
                    compiler_name
                };

                // Sanitize name for Lean: replace invalid characters
                // Lean identifiers can only contain: a-z A-Z 0-9 _ '
                // Move uses: $ # in compiler-generated names
                name = name
                    .replace('$', "_")  // Replace $ with _
                    .replace('#', "_")  // Replace # with _
                    .replace('.', "_"); // Replace . with _ (for fully qualified names)

                // Remove leading underscore if the name starts with one after sanitization
                // (Lean allows leading underscores but it's cleaner without)
                if name.starts_with('_') && name.len() > 1 {
                    name = name[1..].to_string();
                }

                registry.set_name(temp_id, name);
            }
        }
    }
}
