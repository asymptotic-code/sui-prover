// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Statement IR to Lean syntax

use intermediate_theorem_format::{Statement, VariableRegistry, TheoremProgram, PhiVariable, TheoremModuleID, TheoremType};
use super::expression_renderer::ExpressionRenderer;
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;

pub struct StatementRenderer {
    expr_renderer: ExpressionRenderer,
    type_renderer: TypeRenderer,
    expected_return_type: Option<TheoremType>,
}

impl StatementRenderer {
    pub fn new() -> Self {
        Self {
            expr_renderer: ExpressionRenderer::new(),
            type_renderer: TypeRenderer,
            expected_return_type: None,
        }
    }

    pub fn with_return_type(return_type: TheoremType) -> Self {
        Self {
            expr_renderer: ExpressionRenderer::new(),
            type_renderer: TypeRenderer,
            expected_return_type: Some(return_type),
        }
    }

    /// Render an expression to a string
    fn render_expression_to_string<'a>(&self, expr: &intermediate_theorem_format::Expression, registry: &VariableRegistry, program: &TheoremProgram, current_module_id: TheoremModuleID, name_manager: &'a intermediate_theorem_format::NameManager) -> String {
        let writer = LeanWriter::new(name_manager);
        self.expr_renderer.render(expr, registry, program, current_module_id, &writer);
        writer.extract_result()
    }

    /// Check if a branch contains monadic operations
    fn branch_is_monadic(&self, branch: &Statement) -> bool {
        match branch {
            Statement::Sequence(stmts) => stmts.iter().any(|s| s.is_monadic()),
            stmt => stmt.is_monadic(),
        }
    }

    /// Render statements in a branch
    fn render_branch_statements(&mut self, branch: &Statement, registry: &VariableRegistry, program: &TheoremProgram, current_module_id: TheoremModuleID, writer: &LeanWriter) {
        match branch {
            Statement::Sequence(stmts) => {
                for stmt in stmts {
                    self.render(stmt, registry, program, current_module_id, writer);
                    writer.emit("\n");
                }
            }
            stmt => {
                self.render(stmt, registry, program, current_module_id, writer);
                writer.emit("\n");
            }
        }
    }

    /// Render a statement to a LeanWriter
    /// This is the ONLY public rendering method - all statement rendering uses LeanWriter
    pub fn render<'a>(&mut self, stmt: &Statement, registry: &VariableRegistry, program: &TheoremProgram, current_module_id: TheoremModuleID, writer: &LeanWriter<'a>) {
        match stmt {
            Statement::Sequence(stmts) => {
                if stmts.is_empty() {
                    // For native/empty functions, use sorry if return type is not Unit
                    if let Some(ret_type) = &self.expected_return_type {
                        // Check if it's not an empty tuple (unit type)
                        let is_unit = matches!(ret_type, TheoremType::Tuple(v) if v.is_empty());
                        if !is_unit {
                            writer.emit("sorry");
                            return;
                        }
                    }
                    writer.emit("()");
                } else {
                    for (i, s) in stmts.iter().enumerate() {
                        self.render(s, registry, program, current_module_id, writer);
                        if i < stmts.len() - 1 {
                            writer.emit("\n");
                        }
                        // Stop after hitting a terminator
                        if matches!(s, Statement::Return { .. } | Statement::Abort { .. }) {
                            break;
                        }
                    }
                }
            }

            Statement::Let { results, operation, result_types } => {
                let results_str = if results.len() == 1 {
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

                // Check if any result type is ProgramState - if so, use monadic binding
                let is_monadic = result_types.iter().any(|ty| ty.is_monad());

                if is_monadic {
                    writer.emit(&format!("let {} ← ", results_str));
                    self.expr_renderer.render(operation, registry, program, current_module_id, writer);
                } else {
                    writer.emit(&format!("let {} := ", results_str));
                    self.expr_renderer.render(operation, registry, program, current_module_id, writer);
                }
            }

            Statement::If { condition, then_branch, else_branch, phi_vars } => {
                let cond_str = self.render_expression_to_string(condition, registry, program, current_module_id, writer.name_manager);

                // Check if this is a phi-merge if or a statement-level if
                if !phi_vars.is_empty() {
                    // Value-producing if with phi-merge
                    self.render_phi_if(cond_str, then_branch, else_branch, phi_vars, registry, program, current_module_id, writer);
                } else {
                    // Statement-level if for control flow
                    self.render_statement_if(cond_str, then_branch, else_branch, registry, program, current_module_id, writer);
                }
            }

            Statement::While { loop_vars, condition, body } => {
                let init_vals = loop_vars.iter()
                    .map(|v| registry.get_display_name(v.initial_value))
                    .collect::<Vec<_>>();
                let init_tuple = if init_vals.len() == 1 {
                    init_vals[0].clone()
                } else {
                    format!("({})", init_vals.join(", "))
                };

                // Bind the phi_result variables to the loop output
                let phi_results = loop_vars.iter()
                    .map(|v| registry.get_display_name(v.phi_result))
                    .collect::<Vec<_>>();
                let phi_pattern = if phi_results.len() == 1 {
                    phi_results[0].clone()
                } else {
                    format!("({})", phi_results.join(", "))
                };

                // Get the updated values from the loop body
                let updated_vals = loop_vars.iter()
                    .map(|v| registry.get_display_name(v.updated_value))
                    .collect::<Vec<_>>();
                let updated_tuple = if updated_vals.len() == 1 {
                    updated_vals[0].clone()
                } else {
                    format!("({})", updated_vals.join(", "))
                };

                let cond_str = registry.get_display_name(condition.condition_var);

                writer.emit(&format!("let {} ← (whileLoop (fun state => pure {}) (fun state =>\n", phi_pattern, cond_str));
                writer.with_indent(|| {
                    writer.emit("do\n");
                    writer.with_indent(|| {
                        self.render(body, registry, program, current_module_id, writer);
                        // Return the updated values from the loop body
                        writer.emit(&format!("\npure {}", updated_tuple));
                    });
                });
                writer.emit(&format!("\n) {})", init_tuple));
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
                // Convert abort code to Nat since abort expects Nat parameter
                // Use dot notation .toNat which works for all UInt types
                // Wrap in extra parens to prevent line breaks in formatting
                let code_nat = format!("(({}).toNat)", code_str);
                // Use ProgramState.Aborted directly instead of the abort helper
                // This avoids type inference issues with qualified struct names
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
                // Prover requires are for verification only - skip in Lean backend
                // These statements appear in do-blocks, so we need pure ()
                writer.emit("pure ()");
            }

            Statement::Ensures { .. } => {
                // Prover ensures are for verification only - skip in Lean backend
                // These statements appear in do-blocks, so we need pure ()
                writer.emit("pure ()");
            }
        }
    }

    /// Render a statement-level if (no phi variables)
    fn render_statement_if(
        &mut self,
        cond_str: String,
        then_branch: &Statement,
        else_branch: &Statement,
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        writer.emit(&format!("if {} then\n", cond_str));

        writer.with_indent(|| {
            self.render(then_branch, registry, program, current_module_id, writer);
        });

        // Check if else branch has content
        let has_else_content = match else_branch {
            Statement::Sequence(stmts) => !stmts.is_empty(),
            _ => true,
        };

        if has_else_content {
            writer.emit("\nelse\n");
            writer.with_indent(|| {
                self.render(else_branch, registry, program, current_module_id, writer);
            });
        }
    }

    /// Render a value-producing if with phi-merge
    fn render_phi_if(
        &mut self,
        cond_str: String,
        then_branch: &Statement,
        else_branch: &Statement,
        phi_vars: &[PhiVariable],
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        // Check if either branch has monadic operations
        let then_monadic = self.branch_is_monadic(then_branch);
        let else_monadic = self.branch_is_monadic(else_branch);
        // If EITHER branch is monadic, BOTH must be wrapped in do-blocks for type consistency
        let any_monadic = then_monadic || else_monadic;

        // Render phi variable pattern
        let phi_pattern = if phi_vars.len() == 1 {
            registry.get_display_name(phi_vars[0].result)
        } else {
            let names = phi_vars.iter()
                .map(|v| registry.get_display_name(v.result))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", names)
        };

        // Use ← for monadic branches, := for pure branches
        let binding_op = if any_monadic { "←" } else { ":=" };
        writer.emit(&format!("let {} {} if {} then\n", phi_pattern, binding_op, cond_str));

        writer.with_indent(|| {
            // If any branch has monadic operations, wrap in do-block
            if any_monadic {
                writer.emit("do\n");
                writer.with_indent(|| {
                    // Render then branch statements
                    self.render_branch_statements(then_branch, registry, program, current_module_id, writer);
                    // Render return values wrapped in pure
                    self.render_phi_values(&phi_vars.iter().map(|p| &p.then_value).collect::<Vec<_>>(), registry, program, current_module_id, writer);
                });
            } else {
                // Pure branch: render statements and value directly
                self.render_branch_statements(then_branch, registry, program, current_module_id, writer);
                // Render return values
                if phi_vars.len() == 1 {
                    let val_str = self.render_expression_to_string(&phi_vars[0].then_value, registry, program, current_module_id, writer.name_manager);
                    writer.emit(&val_str);
                } else {
                    let vals = phi_vars.iter()
                        .map(|v| self.render_expression_to_string(&v.then_value, registry, program, current_module_id, writer.name_manager))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writer.emit(&format!("({})", vals));
                }
            }
        });

        writer.emit("\nelse\n");

        writer.with_indent(|| {
            // If any branch has monadic operations, wrap in do-block
            if any_monadic {
                writer.emit("do\n");
                writer.with_indent(|| {
                    // Render else branch statements
                    self.render_branch_statements(else_branch, registry, program, current_module_id, writer);
                    // Render return values wrapped in pure
                    self.render_phi_values(&phi_vars.iter().map(|p| &p.else_value).collect::<Vec<_>>(), registry, program, current_module_id, writer);
                });
            } else {
                // Pure branch: render statements and value directly
                self.render_branch_statements(else_branch, registry, program, current_module_id, writer);
                // Render return values
                if phi_vars.len() == 1 {
                    let val_str = self.render_expression_to_string(&phi_vars[0].else_value, registry, program, current_module_id, writer.name_manager);
                    writer.emit(&val_str);
                } else {
                    let vals = phi_vars.iter()
                        .map(|v| self.render_expression_to_string(&v.else_value, registry, program, current_module_id, writer.name_manager))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writer.emit(&format!("({})", vals));
                }
            }
        });
    }

    /// Helper to render phi values with appropriate wrapping
    /// If the value is a monadic call, return it directly; otherwise wrap in pure
    fn render_phi_values(
        &self,
        values: &[&intermediate_theorem_format::Expression],
        registry: &VariableRegistry,
        program: &TheoremProgram,
        current_module_id: TheoremModuleID,
        writer: &LeanWriter,
    ) {
        use intermediate_theorem_format::{Expression, CallConvention};

        // Check if a value is a monadic call
        let is_monadic_call = |expr: &Expression| -> bool {
            matches!(expr, Expression::Call { convention: CallConvention::Monadic, .. })
        };

        if values.len() == 1 {
            let val_str = self.render_expression_to_string(values[0], registry, program, current_module_id, writer.name_manager);
            if is_monadic_call(values[0]) {
                // Already monadic, don't wrap in pure
                writer.emit(&val_str);
            } else {
                writer.emit(&format!("pure {}", val_str));
            }
        } else {
            let vals = values.iter()
                .map(|v| self.render_expression_to_string(v, registry, program, current_module_id, writer.name_manager))
                .collect::<Vec<_>>()
                .join(", ");
            // For tuples, always wrap in pure (monadic calls should be bound before phi merge)
            writer.emit(&format!("pure ({})", vals));
        }
    }
}
