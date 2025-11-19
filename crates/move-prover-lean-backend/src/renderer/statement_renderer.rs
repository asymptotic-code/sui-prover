// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Statement IR to Lean syntax

use intermediate_theorem_format::{Statement, VariableRegistry, TheoremProgram, PhiVariable};
use super::expression_renderer::ExpressionRenderer;
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;

pub struct StatementRenderer {
    expr_renderer: ExpressionRenderer,
    type_renderer: TypeRenderer,
    expected_return_type: Option<String>,
}

impl StatementRenderer {
    pub fn new() -> Self {
        Self {
            expr_renderer: ExpressionRenderer::new(),
            type_renderer: TypeRenderer,
            expected_return_type: None,
        }
    }

    pub fn with_return_type(return_type: String) -> Self {
        Self {
            expr_renderer: ExpressionRenderer::new(),
            type_renderer: TypeRenderer,
            expected_return_type: Some(return_type),
        }
    }

    fn get_var_name(&self, temp_id: u32, registry: &VariableRegistry) -> String {
        registry.get_name(temp_id)
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("t{}", temp_id))
    }

    /// Render an expression to a string
    fn render_expression_to_string<'a>(&self, expr: &intermediate_theorem_format::Expression, registry: &VariableRegistry, program: &TheoremProgram, name_manager: &'a intermediate_theorem_format::NameManager) -> String {
        let writer = LeanWriter::new(name_manager);
        self.expr_renderer.render(expr, registry, program, &writer);
        writer.extract_result()
    }

    /// Extract statements from a branch for phi-merge if-expressions
    /// Returns just the prefix statements - phi values are accessed via the PhiVariable struct
    fn extract_branch_statements(&self, branch: &Statement) -> Vec<Statement> {
        match branch {
            Statement::Sequence(stmts) => {
                // Keep ALL statements in the prefix, filtering empty sequences
                stmts.iter()
                    .filter(|stmt| {
                        !matches!(stmt, Statement::Sequence(s) if s.is_empty())
                    })
                    .cloned()
                    .collect()
            }
            _ => vec![branch.clone()],
        }
    }

    /// Render a statement to a LeanWriter
    /// This is the ONLY public rendering method - all statement rendering uses LeanWriter
    pub fn render<'a>(&mut self, stmt: &Statement, registry: &VariableRegistry, program: &TheoremProgram, writer: &LeanWriter<'a>) {
        match stmt {
            Statement::Sequence(stmts) => {
                if stmts.is_empty() {
                    // For native/empty functions, use sorry if return type is not Unit
                    if let Some(ret_type) = &self.expected_return_type {
                        if ret_type != "Unit" {
                            writer.emit("sorry");
                            return;
                        }
                    }
                    writer.emit("()");
                } else {
                    for (i, s) in stmts.iter().enumerate() {
                        self.render(s, registry, program, writer);
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

            Statement::Let { results, operation, .. } => {
                let results_str = if results.len() == 1 {
                    let var_name = self.get_var_name(results[0], registry);
                    if var_name == "()" { "_".to_string() } else { var_name }
                } else {
                    let temps = results.iter()
                        .map(|r| {
                            let var_name = self.get_var_name(*r, registry);
                            if var_name == "()" { "_".to_string() } else { var_name }
                        })
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("({})", temps)
                };

                let is_monadic = operation.is_monadic();

                if is_monadic {
                    writer.emit(&format!("let {} ← ", results_str));
                    self.expr_renderer.render(operation, registry, program, writer);
                } else {
                    writer.emit(&format!("let {} := ", results_str));
                    self.expr_renderer.render(operation, registry, program, writer);
                }
            }

            Statement::If { condition, then_branch, else_branch, phi_vars } => {
                let cond_str = self.render_expression_to_string(condition, registry, program, writer.name_manager);

                // Check if this is a phi-merge if or a statement-level if
                if !phi_vars.is_empty() {
                    // Value-producing if with phi-merge
                    self.render_phi_if(cond_str, then_branch, else_branch, phi_vars, registry, program, writer);
                } else {
                    // Statement-level if for control flow
                    self.render_statement_if(cond_str, then_branch, else_branch, registry, program, writer);
                }
            }

            Statement::While { loop_vars, condition, body } => {
                let init_vals = loop_vars.iter()
                    .map(|v| self.get_var_name(v.initial_value, registry))
                    .collect::<Vec<_>>();
                let init_tuple = if init_vals.len() == 1 {
                    init_vals[0].clone()
                } else {
                    format!("({})", init_vals.join(", "))
                };

                // Bind the phi_result variables to the loop output
                let phi_results = loop_vars.iter()
                    .map(|v| self.get_var_name(v.phi_result, registry))
                    .collect::<Vec<_>>();
                let phi_pattern = if phi_results.len() == 1 {
                    phi_results[0].clone()
                } else {
                    format!("({})", phi_results.join(", "))
                };

                // Get the updated values from the loop body
                let updated_vals = loop_vars.iter()
                    .map(|v| self.get_var_name(v.updated_value, registry))
                    .collect::<Vec<_>>();
                let updated_tuple = if updated_vals.len() == 1 {
                    updated_vals[0].clone()
                } else {
                    format!("({})", updated_vals.join(", "))
                };

                let cond_str = self.render_expression_to_string(condition, registry, program, writer.name_manager);

                writer.emit(&format!("let {} ← (whileLoop (fun state => pure {}) (fun state =>\n", phi_pattern, cond_str));
                writer.with_indent(|| {
                    writer.emit("do\n");
                    writer.with_indent(|| {
                        self.render(body, registry, program, writer);
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
                    let val_str = self.render_expression_to_string(&values[0], registry, program, writer.name_manager);
                    writer.emit(&format!("pure {}", val_str));
                } else {
                    let vals = values.iter()
                        .map(|v| self.render_expression_to_string(v, registry, program, writer.name_manager))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writer.emit(&format!("pure ({})", vals));
                }
            }

            Statement::Abort { code } => {
                let code_str = self.render_expression_to_string(code, registry, program, writer.name_manager);
                if let Some(ret_type) = &self.expected_return_type {
                    let inner_type = if ret_type.starts_with("(ProgramState ") && ret_type.ends_with(")") {
                        &ret_type[14..ret_type.len()-1]
                    } else if ret_type.starts_with("ProgramState ") {
                        &ret_type[13..]
                    } else {
                        ret_type.as_str()
                    };
                    writer.emit(&format!("(@abort {} {})", inner_type, code_str));
                } else {
                    writer.emit(&format!("abort {}", code_str));
                }
            }

            Statement::UpdateField { target, struct_id, field_index, new_value } => {
                let target_str = self.render_expression_to_string(target, registry, program, writer.name_manager);
                let value_str = self.render_expression_to_string(new_value, registry, program, writer.name_manager);

                let struct_info = program.structs.get(struct_id);
                let field_name = if let Some(info) = struct_info {
                    info.fields.get(*field_index)
                        .map(|f| f.name.clone())
                        .unwrap_or_else(|| format!("field{}", field_index))
                } else {
                    format!("field{}", field_index)
                };

                writer.emit(&format!("let {} := {{ {} with {} := {} }}",
                    target_str,
                    target_str,
                    field_name,
                    value_str));
            }

            Statement::UpdateVectorElement { target, index, new_value } => {
                let target_str = self.render_expression_to_string(target, registry, program, writer.name_manager);
                let index_str = self.render_expression_to_string(index, registry, program, writer.name_manager);
                let value_str = self.render_expression_to_string(new_value, registry, program, writer.name_manager);

                writer.emit(&format!("let {} := {}.set {} {}",
                    target_str,
                    target_str,
                    index_str,
                    value_str));
            }

            Statement::Requires { condition } => {
                let cond_str = self.render_expression_to_string(condition, registry, program, writer.name_manager);
                writer.emit(&format!("_ ← prover_requires {}", cond_str));
            }

            Statement::Ensures { condition } => {
                let cond_str = self.render_expression_to_string(condition, registry, program, writer.name_manager);
                writer.emit(&format!("_ ← prover_ensures {}", cond_str));
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
        writer: &LeanWriter,
    ) {
        writer.emit(&format!("if {} then\n", cond_str));

        writer.with_indent(|| {
            self.render(then_branch, registry, program, writer);
        });

        // Check if else branch has content
        let has_else_content = match else_branch {
            Statement::Sequence(stmts) => !stmts.is_empty(),
            _ => true,
        };

        if has_else_content {
            writer.emit("\nelse\n");
            writer.with_indent(|| {
                self.render(else_branch, registry, program, writer);
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
        writer: &LeanWriter,
    ) {
        // Extract prefix statements
        let then_prefix = self.extract_branch_statements(then_branch);
        let else_prefix = self.extract_branch_statements(else_branch);

        // Check if either branch has monadic operations
        let then_monadic = then_prefix.iter().any(|s| s.is_monadic());
        let else_monadic = else_prefix.iter().any(|s| s.is_monadic());
        // If EITHER branch is monadic, BOTH must be wrapped in do-blocks for type consistency
        let any_monadic = then_monadic || else_monadic;

        // Render phi variable pattern
        let phi_pattern = if phi_vars.len() == 1 {
            self.get_var_name(phi_vars[0].result, registry)
        } else {
            let names = phi_vars.iter()
                .map(|v| self.get_var_name(v.result, registry))
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
                    for stmt in &then_prefix {
                        self.render(stmt, registry, program, writer);
                        writer.emit("\n");
                    }
                    // Render return values wrapped in pure
                    self.render_phi_values(&phi_vars.iter().map(|p| &p.then_value).collect::<Vec<_>>(), registry, program, writer);
                });
            } else {
                // Pure branch: render statements and value directly
                for stmt in &then_prefix {
                    self.render(stmt, registry, program, writer);
                    writer.emit("\n");
                }
                // Render return values
                if phi_vars.len() == 1 {
                    let val_str = self.render_expression_to_string(&phi_vars[0].then_value, registry, program, writer.name_manager);
                    writer.emit(&val_str);
                } else {
                    let vals = phi_vars.iter()
                        .map(|v| self.render_expression_to_string(&v.then_value, registry, program, writer.name_manager))
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
                    for stmt in &else_prefix {
                        self.render(stmt, registry, program, writer);
                        writer.emit("\n");
                    }
                    // Render return values wrapped in pure
                    self.render_phi_values(&phi_vars.iter().map(|p| &p.else_value).collect::<Vec<_>>(), registry, program, writer);
                });
            } else {
                // Pure branch: render statements and value directly
                for stmt in &else_prefix {
                    self.render(stmt, registry, program, writer);
                    writer.emit("\n");
                }
                // Render return values
                if phi_vars.len() == 1 {
                    let val_str = self.render_expression_to_string(&phi_vars[0].else_value, registry, program, writer.name_manager);
                    writer.emit(&val_str);
                } else {
                    let vals = phi_vars.iter()
                        .map(|v| self.render_expression_to_string(&v.else_value, registry, program, writer.name_manager))
                        .collect::<Vec<_>>()
                        .join(", ");
                    writer.emit(&format!("({})", vals));
                }
            }
        });
    }

    /// Helper to render phi values with appropriate wrapping
    /// If any value is monadic, return it directly; otherwise wrap in pure
    fn render_phi_values(
        &self,
        values: &[&intermediate_theorem_format::Expression],
        registry: &VariableRegistry,
        program: &TheoremProgram,
        writer: &LeanWriter,
    ) {
        // Check if any value is monadic
        let any_monadic = values.iter().any(|v| v.is_monadic());

        if values.len() == 1 {
            let val_str = self.render_expression_to_string(values[0], registry, program, writer.name_manager);
            if values[0].is_monadic() {
                // Already monadic, don't wrap in pure
                writer.emit(&val_str);
            } else {
                writer.emit(&format!("pure {}", val_str));
            }
        } else {
            let vals = values.iter()
                .map(|v| self.render_expression_to_string(v, registry, program, writer.name_manager))
                .collect::<Vec<_>>()
                .join(", ");
            if any_monadic {
                // At least one is monadic - need to handle this case
                // For now, just return the tuple directly (this might need more sophisticated handling)
                writer.emit(&format!("pure ({})", vals));
            } else {
                writer.emit(&format!("pure ({})", vals));
            }
        }
    }
}
