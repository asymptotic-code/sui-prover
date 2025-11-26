// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Statement IR to Lean syntax

use intermediate_theorem_format::{Statement, VariableRegistry, TheoremProgram, TheoremModuleID, TheoremType, Expression, Block, CallConvention};
use super::expression_renderer::ExpressionRenderer;
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;

pub struct StatementRenderer {
    expr_renderer: ExpressionRenderer,
    type_renderer: TypeRenderer,
    expected_return_type: Option<TheoremType>,
    /// Track if we're at the top-level function body (true) or in a nested context (false)
    is_top_level: bool,
}

impl StatementRenderer {
    pub fn new() -> Self {
        Self {
            expr_renderer: ExpressionRenderer::new(),
            type_renderer: TypeRenderer,
            expected_return_type: None,
            is_top_level: true,
        }
    }

    pub fn with_return_type(return_type: TheoremType) -> Self {
        Self {
            expr_renderer: ExpressionRenderer::new(),
            type_renderer: TypeRenderer,
            expected_return_type: Some(return_type),
            is_top_level: true,
        }
    }

    /// Render an expression to a string
    fn render_expression_to_string<'a>(&self, expr: &Expression, registry: &VariableRegistry, program: &TheoremProgram, current_module_id: TheoremModuleID, name_manager: &'a intermediate_theorem_format::NameManager) -> String {
        let writer = LeanWriter::new(name_manager);
        self.expr_renderer.render(expr, registry, program, current_module_id, &writer);
        writer.extract_result()
    }

    /// Check if an expression contains monadic operations
    fn expr_is_monadic(&self, expr: &Expression) -> bool {
        match expr {
            Expression::Call { convention: CallConvention::Monadic, .. } => true,
            Expression::IfExpr { then_block, else_block, .. } => {
                then_block.is_monadic() || else_block.is_monadic()
            }
            Expression::WhileExpr { .. } => true, // While is always monadic in our model
            _ => false,
        }
    }

    /// Check if a block contains monadic operations
    fn block_is_monadic(&self, block: &Block) -> bool {
        block.statements.iter().any(|s| s.is_monadic()) || self.expr_is_monadic(&block.result)
    }

    /// Render a statement to a LeanWriter
    pub fn render<'a>(&mut self, stmt: &Statement, registry: &VariableRegistry, program: &TheoremProgram, current_module_id: TheoremModuleID, writer: &LeanWriter<'a>) {
        match stmt {
            Statement::Sequence(stmts) => {
                if stmts.is_empty() {
                    if self.is_top_level {
                        if let Some(ret_type) = &self.expected_return_type {
                            let is_unit = matches!(ret_type, TheoremType::Tuple(v) if v.is_empty());
                            if !is_unit {
                                writer.emit("sorry");
                                return;
                            }
                        }
                        writer.emit("()");
                    }
                } else {
                    for (i, s) in stmts.iter().enumerate() {
                        self.render(s, registry, program, current_module_id, writer);
                        if i < stmts.len() - 1 {
                            writer.emit("\n");
                        }
                        if matches!(s, Statement::Return { .. } | Statement::Abort { .. }) {
                            break;
                        }
                    }
                }
            }

            Statement::Let { results, operation, result_types } => {
                // Check if operation is IfExpr or WhileExpr - these get special handling
                match operation {
                    Expression::IfExpr { condition, then_block, else_block } => {
                        self.render_if_expr(results, result_types, condition, then_block, else_block, registry, program, current_module_id, writer);
                    }
                    Expression::WhileExpr { condition, body, state } => {
                        self.render_while_expr(results, result_types, condition, body, state, registry, program, current_module_id, writer);
                    }
                    _ => {
                        // Normal let binding
                        let results_str = if results.is_empty() {
                            "_".to_string()
                        } else if results.len() == 1 {
                            let var_name = registry.get_display_name(results[0]);
                            if var_name == "()" { "_".to_string() } else { var_name }
                        } else {
                            let temps = results.iter()
                                .map(|r| {
                                    let var_name = registry.get_display_name(*r);
                                    if var_name == "()" { "_".to_string() } else { var_name }
                                })
                                .collect::<Vec<_>>()
                                .join(", ");
                            format!("({})", temps)
                        };

                        let is_monadic = result_types.iter().any(|ty| ty.is_monad());

                        if is_monadic {
                            writer.emit(&format!("let {} ← ", results_str));
                            self.expr_renderer.render(operation, registry, program, current_module_id, writer);
                        } else {
                            writer.emit(&format!("let {} := ", results_str));
                            self.expr_renderer.render(operation, registry, program, current_module_id, writer);
                        }
                    }
                }
            }

            Statement::Return { values } => {
                if values.is_empty() {
                    writer.emit("pure ()");
                } else if values.len() == 1 {
                    let val_str = self.render_expression_to_string(&values[0], registry, program, current_module_id, writer.name_manager);
                    writer.emit(&format!("pure {}", val_str));
                } else {
                    let vals = values.iter()
                        .map(|v| self.render_expression_to_string(v, registry, program, current_module_id, writer.name_manager))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writer.emit(&format!("pure ({})", vals));
                }
            }

            Statement::Abort { code } => {
                let code_str = self.render_expression_to_string(code, registry, program, current_module_id, writer.name_manager);
                let code_nat = format!("(({}).toNat)", code_str);
                writer.emit(&format!("ProgramState.Aborted {}", code_nat));
            }

            Statement::UpdateField { target, struct_id, field_index, new_value } => {
                let target_str = self.render_expression_to_string(target, registry, program, current_module_id, writer.name_manager);
                let value_str = self.render_expression_to_string(new_value, registry, program, current_module_id, writer.name_manager);

                let struct_info = program.structs.get(struct_id);
                let field_name = if let Some(info) = struct_info {
                    info.fields.get(*field_index)
                        .map(|f| f.name.clone())
                        .unwrap_or_else(|| panic!("BUG: Field index {} out of bounds for struct", field_index))
                } else {
                    panic!("BUG: Missing struct info when unpacking struct field");
                };

                writer.emit(&format!("let {} := {{ {} with {} := {} }}",
                    target_str,
                    target_str,
                    field_name,
                    value_str));
            }

            Statement::UpdateVectorElement { target, index, new_value } => {
                let target_str = self.render_expression_to_string(target, registry, program, current_module_id, writer.name_manager);
                let index_str = self.render_expression_to_string(index, registry, program, current_module_id, writer.name_manager);
                let value_str = self.render_expression_to_string(new_value, registry, program, current_module_id, writer.name_manager);

                writer.emit(&format!("let {} := {}.set {} {}",
                    target_str,
                    target_str,
                    index_str,
                    value_str));
            }

            Statement::Requires { .. } => {
                writer.emit("pure ()");
            }

            Statement::Ensures { .. } => {
                writer.emit("pure ()");
            }
        }
    }

    /// Render an if expression bound to results
    fn render_if_expr(
        &mut self,
        results: &[intermediate_theorem_format::TempId],
        result_types: &[TheoremType],
        condition: &Expression,
        then_block: &Block,
        else_block: &Block,
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        let cond_str = self.render_expression_to_string(condition, registry, program, current_module_id, writer.name_manager);

        // Check if any branch has monadic operations
        let then_monadic = self.block_is_monadic(then_block);
        let else_monadic = self.block_is_monadic(else_block);
        let any_monadic = then_monadic || else_monadic;

        // Check if both branches terminate (Return/Abort)
        // In this case, don't bind to a variable - the if IS the return
        let both_terminate = then_block.terminates() && else_block.terminates();

        // Build the result pattern
        let result_pattern = if results.is_empty() {
            "_".to_string()
        } else if results.len() == 1 {
            registry.get_display_name(results[0])
        } else {
            let names = results.iter()
                .map(|r| registry.get_display_name(*r))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", names)
        };

        // When both branches terminate, emit the if without binding
        if both_terminate && results.is_empty() {
            writer.emit(&format!("if {} then\n", cond_str));
        } else {
            // Use ← for monadic branches, := for pure branches
            let binding_op = if any_monadic { "←" } else { ":=" };
            writer.emit(&format!("let {} {} if {} then\n", result_pattern, binding_op, cond_str));
        }

        // Render then branch
        writer.with_indent(|| {
            if any_monadic {
                writer.emit("do\n");
                writer.with_indent(|| {
                    self.render_block_contents(then_block, !then_block.terminates(), any_monadic, registry, program, current_module_id, writer);
                });
            } else {
                // For pure branches, still don't emit result if block terminates
                self.render_block_contents(then_block, !then_block.terminates(), false, registry, program, current_module_id, writer);
            }
        });

        writer.emit("\nelse\n");

        // Render else branch
        writer.with_indent(|| {
            if any_monadic {
                writer.emit("do\n");
                writer.with_indent(|| {
                    self.render_block_contents(else_block, !else_block.terminates(), any_monadic, registry, program, current_module_id, writer);
                });
            } else {
                // For pure branches, still don't emit result if block terminates
                self.render_block_contents(else_block, !else_block.terminates(), false, registry, program, current_module_id, writer);
            }
        });
    }

    /// Render a while expression bound to results
    fn render_while_expr(
        &mut self,
        results: &[intermediate_theorem_format::TempId],
        result_types: &[TheoremType],
        condition: &Block,
        body: &Block,
        state: &intermediate_theorem_format::LoopState,
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        // Build the result pattern (loop outputs)
        let result_pattern = if results.is_empty() {
            "_".to_string()
        } else if results.len() == 1 {
            registry.get_display_name(results[0])
        } else {
            let names = results.iter()
                .map(|r| registry.get_display_name(*r))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", names)
        };

        // Build state variable pattern
        let state_pattern = if state.vars.is_empty() {
            "_".to_string()
        } else if state.vars.len() == 1 {
            registry.get_display_name(state.vars[0])
        } else {
            let names = state.vars.iter()
                .map(|v| registry.get_display_name(*v))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", names)
        };

        // Build initial values tuple
        let init_tuple = if state.initial.is_empty() {
            "()".to_string()
        } else if state.initial.len() == 1 {
            self.render_expression_to_string(&state.initial[0], registry, program, current_module_id, writer.name_manager)
        } else {
            let vals = state.initial.iter()
                .map(|e| self.render_expression_to_string(e, registry, program, current_module_id, writer.name_manager))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", vals)
        };

        // Render the while loop
        writer.emit(&format!("let {} ← (whileLoop (fun {} =>\n", result_pattern, state_pattern));
        writer.with_indent(|| {
            writer.emit("do\n");
            writer.with_indent(|| {
                // Render condition computation statements
                self.render_block_statements(&condition.statements, registry, program, current_module_id, writer);
                // Return the condition value
                let cond_str = self.render_expression_to_string(&condition.result, registry, program, current_module_id, writer.name_manager);
                writer.emit(&format!("\npure {}", cond_str));
            });
        });
        writer.emit(&format!(") (fun {} =>\n", state_pattern));
        writer.with_indent(|| {
            writer.emit("do\n");
            writer.with_indent(|| {
                // Render body statements
                self.render_block_statements(&body.statements, registry, program, current_module_id, writer);
                // Return the updated state
                let body_result_str = self.render_expression_to_string(&body.result, registry, program, current_module_id, writer.name_manager);
                writer.emit(&format!("\npure {}", body_result_str));
            });
        });
        writer.emit(&format!("\n) {})", init_tuple));
    }

    /// Render block contents (statements + result)
    fn render_block_contents(
        &mut self,
        block: &Block,
        emit_result: bool,
        wrap_in_pure: bool,
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        let old_is_top_level = self.is_top_level;
        self.is_top_level = false;

        // Render statements
        self.render_block_statements(&block.statements, registry, program, current_module_id, writer);

        // Render result if needed
        if emit_result {
            if !block.statements.is_empty() {
                writer.emit("\n");
            }
            let result_str = self.render_expression_to_string(&block.result, registry, program, current_module_id, writer.name_manager);
            if wrap_in_pure {
                writer.emit(&format!("pure {}", result_str));
            } else {
                writer.emit(&result_str);
            }
        }

        self.is_top_level = old_is_top_level;
    }

    /// Render block statements (without the result)
    fn render_block_statements(
        &mut self,
        statements: &[Statement],
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        let old_is_top_level = self.is_top_level;
        self.is_top_level = false;

        for (i, stmt) in statements.iter().enumerate() {
            self.render(stmt, registry, program, current_module_id, writer);
            if i < statements.len() - 1 {
                writer.emit("\n");
            }
        }

        self.is_top_level = old_is_top_level;
    }
}
