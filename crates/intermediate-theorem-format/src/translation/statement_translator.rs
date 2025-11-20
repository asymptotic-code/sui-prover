// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Translates StructuredBlock CFG to Statement IR
//!
//! Single responsibility: Convert structured control flow to Statement trees.
//! Uses ExpressionTranslator for bytecode operations.

use crate::data::statements::Statement;
use crate::data::functions::LoopVariable;
use crate::data::types::{TempId, TheoremType};
use crate::data::variables::VariableRegistry;
use crate::data::expressions::Expression;
use crate::translation::expression_translator::ExpressionTranslator;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, BorrowNode, BorrowEdge};
use move_stackless_bytecode::borrow_analysis::BorrowAnnotation;
use move_stackless_bytecode::function_target::FunctionTarget;
use move_model::model::GlobalEnv;
use move_binary_format::file_format::CodeOffset;

pub struct StatementTranslator<'env, 'a> {
    expr_translator: &'a ExpressionTranslator<'env>,
    code: &'a [Bytecode],
    target: &'a FunctionTarget<'a>,
}

impl<'env, 'a> StatementTranslator<'env, 'a> {
    pub fn new(
        _env: &'env GlobalEnv,
        expr_translator: &'a ExpressionTranslator<'env>,
        code: &'a [Bytecode],
        target: &'a FunctionTarget<'a>,
    ) -> Self {
        Self {
            expr_translator,
            code,
            target,
        }
    }

    /// Translate WriteRef operation using borrow analysis
    /// Returns the update statement based on what the reference borrows from
    fn translate_write_ref(
        &self,
        offset: CodeOffset,
        ref_temp: usize,
        value_temp: usize,
        registry: &VariableRegistry,
    ) -> Statement {
        // Get borrow annotation from function target
        let borrow_annotation = self.target.get_annotations().get::<BorrowAnnotation>();

        if borrow_annotation.is_none() {
            // No borrow annotation - fall back to simple assignment
            // This happens when the transformation pipeline wasn't run
            let local_type = registry.get_type(ref_temp as TempId)
                .cloned()
                .unwrap_or(TheoremType::Bool);

            return Statement::Let {
                results: vec![ref_temp as TempId],
                operation: crate::Expression::Temporary(value_temp as TempId),
                result_types: vec![local_type],
            };
        }

        let borrow_info_at_offset = borrow_annotation
            .and_then(|ann| ann.get_borrow_info_at(offset));

        if borrow_info_at_offset.is_none() {
            panic!("BUG: No borrow info at offset {} for WriteRef", offset);
        }

        let borrow_info = &borrow_info_at_offset.unwrap().before;

        // Find what this reference borrows from using the public API
        let ref_node = BorrowNode::Reference(ref_temp);

        // Use public API: get_incoming returns parents with edges
        let incoming = borrow_info.get_incoming(&ref_node);

        if incoming.is_empty() {
            // Reference has no incoming edges - it's a function parameter
            // Check if this is indeed a parameter
            if ref_temp < self.target.get_parameter_count() {
                // Reference parameter: function should return updated value
                // Generate: let param := new_value
                let param_type = registry.get_type(ref_temp as TempId)
                    .cloned()
                    .unwrap_or(TheoremType::Bool);

                return Statement::Let {
                    results: vec![ref_temp as TempId],
                    operation: crate::Expression::Temporary(value_temp as TempId),
                    result_types: vec![param_type],
                };
            } else {
                panic!("BUG: WriteRef to reference {} with no incoming edges and not a parameter", ref_temp);
            }
        }

        // Get the first (and should be only) parent
        let (parent_node, edge) = incoming.first().unwrap();

        // Match on parent and edge to determine update type
        match (parent_node, edge) {
            (BorrowNode::LocalRoot(local_idx), BorrowEdge::Direct) => {
                // Direct borrow: &mut x
                // Generate: let x := value
                let local_type = registry.get_type(*local_idx as TempId)
                    .cloned()
                    .unwrap_or(TheoremType::Bool);

                Statement::Let {
                    results: vec![*local_idx as TempId],
                    operation: crate::Expression::Temporary(value_temp as TempId),
                    result_types: vec![local_type],
                }
            }

            (BorrowNode::LocalRoot(local_idx), BorrowEdge::Field(struct_qid, field_idx)) => {
                // Field borrow: &mut struct.field
                // Generate: UpdateField statement
                let struct_id = self.expr_translator.resolve_struct_id(
                    struct_qid.module_id,
                    struct_qid.id,
                );

                Statement::UpdateField {
                    target: Expression::Temporary(*local_idx as TempId),
                    struct_id,
                    field_index: *field_idx,
                    new_value: Expression::Temporary(value_temp as TempId),
                }
            }

            (BorrowNode::LocalRoot(_local_idx), BorrowEdge::Index(_index_kind)) => {
                // Vector element borrow: &mut vec[i]
                unimplemented!("Vector element WriteRef not yet implemented - need to track index temp from BorrowLoc")
            }

            (BorrowNode::LocalRoot(_local_idx), BorrowEdge::Hyper(_edges)) => {
                // Nested borrow: &mut struct.inner.field or &mut vec[i].field
                unimplemented!("Nested field WriteRef (Hyper edge) not yet implemented")
            }

            (BorrowNode::LocalRoot(_local_idx), BorrowEdge::DynamicField(..)) => {
                // Dynamic field borrow: &mut borrow_mut_dynamic_field(...)
                unimplemented!("Dynamic field WriteRef not yet implemented - requires explicit map model")
            }

            (BorrowNode::GlobalRoot(_), _) => {
                // Global borrow: &mut borrow_global_mut<T>(addr)
                unimplemented!("Global WriteRef not yet implemented - requires explicit memory model")
            }

            _ => {
                panic!("BUG: Unsupported WriteRef pattern: parent={:?}, edge={:?}", parent_node, edge);
            }
        }
    }

    /// Translate a range of bytecode instructions to a statement
    pub fn translate_block(
        &self,
        lower: CodeOffset,
        upper: CodeOffset,
        registry: &mut VariableRegistry,
    ) -> Statement {
        let mut statements = Vec::new();

        for offset in lower..=upper {
            if offset >= self.code.len() as u16 {
                break;
            }

            let bytecode = &self.code[offset as usize];

            // Handle control flow and special statements
            match bytecode {
                Bytecode::Ret(_, temps) => {
                    let values = temps.iter().map(|&t| Expression::Temporary(t as TempId)).collect();
                    statements.push(Statement::Return { values });
                    // Stop processing after return - any subsequent code is unreachable
                    break;
                }

                Bytecode::Abort(_, temp) => {
                    statements.push(Statement::Abort {
                        code: Expression::Temporary(*temp as TempId),
                    });
                    // Stop processing after abort - any subsequent code is unreachable
                    break;
                }

                Bytecode::Label(_, _)
                | Bytecode::Jump(_, _)
                | Bytecode::Branch(_, _, _, _)
                | Bytecode::Nop(_) => {
                    // These are handled by CFG reconstruction, skip
                }

                // Handle WriteRef specially using borrow analysis
                Bytecode::Call(_, _, operation, srcs, _)
                    if matches!(operation, move_stackless_bytecode::stackless_bytecode::Operation::WriteRef) =>
                {

                    if srcs.len() != 2 {
                        panic!("BUG: WriteRef expects 2 sources, got {}", srcs.len());
                    }

                    let ref_temp = srcs[0];
                    let value_temp = srcs[1];

                    let stmt = self.translate_write_ref(offset, ref_temp, value_temp, registry);
                    statements.push(stmt);
                }

                // Handle Unpack specially - create separate Let for each field
                Bytecode::Call(_, dests, operation, srcs, _)
                    if matches!(operation, move_stackless_bytecode::stackless_bytecode::Operation::Unpack(..)) =>
                {
                    use move_stackless_bytecode::stackless_bytecode::Operation;

                    if let Operation::Unpack(module_id, struct_id, _type_args) = operation {
                        if srcs.is_empty() {
                            panic!("BUG: Unpack operation with no source");
                        }

                        let struct_id_ir = self.expr_translator.resolve_struct_id(*module_id, *struct_id);
                        let source_temp = srcs[0];

                        // Create one Let statement per field
                        for (field_index, &dest_temp) in dests.iter().enumerate() {
                            let dest_type = registry
                                .get_type(dest_temp as TempId)
                                .cloned()
                                .unwrap_or(TheoremType::Bool);

                            let operation = crate::Expression::Unpack {
                                struct_id: struct_id_ir,
                                field_index,
                                operand: Box::new(crate::Expression::Temporary(source_temp as TempId)),
                            };

                            statements.push(Statement::Let {
                                results: vec![dest_temp as TempId],
                                operation,
                                result_types: vec![dest_type],
                            });
                        }
                    }
                }

                _ => {
                    // Try to convert to expression
                    if let Some(expr) = self.expr_translator.translate(bytecode, registry) {
                        // Get destination temps - handle both Call and Assign bytecodes
                        let dests_vec: Vec<usize>;
                        let dests: &[usize] = match bytecode {
                            Bytecode::Call(_, dests, _, _, _) => dests.as_slice(),
                            Bytecode::Assign(_, dest, _, _) => {
                                dests_vec = vec![*dest];
                                &dests_vec
                            }
                            Bytecode::Load(_, dest, _) => {
                                dests_vec = vec![*dest];
                                &dests_vec
                            }
                            _ => &[],
                        };

                        if !dests.is_empty() {
                            let results: Vec<TempId> = dests.iter().map(|&t| t as TempId).collect();

                            // Get types for results
                            let result_types: Vec<TheoremType> = results
                                .iter()
                                .map(|&temp_id| {
                                    registry
                                        .get_type(temp_id)
                                        .cloned()
                                        .unwrap_or(TheoremType::Bool) // Fallback
                                })
                                .collect();

                            statements.push(Statement::Let {
                                results,
                                operation: expr,
                                result_types,
                            });
                        }
                    }
                }
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

    /// Build a While statement with proper loop variables
    pub fn build_while(
        &self,
        condition_temp: TempId,
        _condition_stmt: Statement,
        body_stmt: Statement,
        phi_nodes: &[(usize, usize, usize)], // (phi_result, initial, updated)
        registry: &VariableRegistry,
    ) -> Statement {
        let loop_vars: Vec<LoopVariable> = phi_nodes
            .iter()
            .map(|&(phi_result, initial, updated)| {
                let var_type = registry
                    .get_type(phi_result as TempId)
                    .cloned()
                    .unwrap_or(TheoremType::Bool);

                LoopVariable {
                    phi_result: phi_result as TempId,
                    initial_value: initial as TempId,
                    updated_value: updated as TempId,
                    var_type,
                }
            })
            .collect();

        Statement::While {
            loop_vars,
            condition: Expression::Temporary(condition_temp),
            body: Box::new(body_stmt),
        }
    }

    /// Build an If statement
    pub fn build_if(
        &self,
        condition_temp: TempId,
        then_branch: Statement,
        else_branch: Option<Statement>,
    ) -> Statement {
        Statement::If {
            condition: Expression::Temporary(condition_temp),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch.unwrap_or(Statement::Sequence(vec![]))),
            phi_vars: vec![],  // No phi variables in statement translator
        }
    }

    /// Build a Sequence statement
    pub fn build_sequence(&self, statements: Vec<Statement>) -> Statement {
        match statements.len() {
            0 => Statement::Sequence(vec![]),
            1 => statements.into_iter().next().unwrap(),
            _ => Statement::Sequence(statements),
        }
    }
}
