// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Renders Expression IR to Lean syntax

use intermediate_theorem_format::{Expression, BinOp, UnOp, VariableRegistry, TheoremProgram, ConstantValue, TheoremModuleID};
use super::type_renderer::TypeRenderer;
use super::lean_writer::LeanWriter;
use crate::escape;

pub struct ExpressionRenderer {
    type_renderer: TypeRenderer,
}

impl ExpressionRenderer {
    pub fn new() -> Self {
        Self {
            type_renderer: TypeRenderer,
        }
    }

    /// Capitalize the first letter of a string (for Lean naming conventions)
    fn capitalize_first(s: &str) -> String {
        let mut chars = s.chars();
        match chars.next() {
            None => String::new(),
            Some(first) => {
                let mut result = first.to_uppercase().collect::<String>();
                result.push_str(chars.as_str());
                result
            }
        }
    }

    /// Render expression to a writer
    /// current_module_id: ID of the module we're currently rendering (for determining if function calls need qualification)
    pub fn render(&self, expr: &Expression, registry: &VariableRegistry, program: &TheoremProgram, current_module_id: TheoremModuleID, writer: &LeanWriter) {
        match expr {
            Expression::Temporary(temp_id) => {
                writer.emit(&registry.get_display_name(*temp_id));
            }

            Expression::Constant(value) => {
                // CRITICAL: UInt constants need type annotations to prevent Lean from
                // inferring them as Nat, which causes type errors in operations
                // Always annotate to preserve exact Move types
                match value {
                    ConstantValue::UInt { bits, value: v } => {
                        // Map bit width to Lean type name
                        let type_name = match bits {
                            8 => "UInt8",
                            16 => "UInt16",
                            32 => "UInt32",
                            64 => "UInt64",
                            128 => "UInt128",
                            256 => "UInt256",
                            _ => unreachable!(),
                        };

                        // Always annotate all UInt constants to preserve Move type information
                        writer.emit("(");
                        writer.emit(&v.to_string());
                        writer.emit(" : ");
                        writer.emit(type_name);
                        writer.emit(")");
                    }
                    _ => {
                        writer.emit(&value.to_string());
                    }
                }
            }

            Expression::BinOp { op, lhs, rhs } => {
                match op {
                    // Arithmetic operators - infix notation
                    BinOp::Add => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" + ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Sub => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" - ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Mul => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" * ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Div => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" / ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Mod => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" % ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }

                    // Bitwise operators - use &&& ||| ^^^ for bit operations
                    BinOp::BitAnd => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" &&& ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::BitOr => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" ||| ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::BitXor => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" ^^^ ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    // Shift operators - use HShiftLeft/HShiftRight instances from Helpers.lean
                    // These instances handle type conversion from Nat/UInt* to the appropriate shift amount
                    BinOp::Shl => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" <<< ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Shr => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" >>> ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }

                    // Logical operators - && and || work on Bool in Lean
                    BinOp::And => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" && ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Or => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" || ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }

                    // Comparison operators - use decidable equality (==, !=)
                    // These produce Bool via the Decidable typeclass
                    BinOp::Eq => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" == ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    BinOp::Neq => {
                        writer.emit("(");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" != ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }

                    // Ordering comparisons - use decidable comparisons
                    // In Lean 4, < <= > >= on Nat/Int produce Prop, but we need Bool
                    // Use decide to convert Prop to Bool for decidable instances
                    BinOp::Lt => {
                        writer.emit("(decide (");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" < ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit("))");
                    }
                    BinOp::Le => {
                        writer.emit("(decide (");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" ≤ ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit("))");
                    }
                    BinOp::Gt => {
                        writer.emit("(decide (");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" > ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit("))");
                    }
                    BinOp::Ge => {
                        writer.emit("(decide (");
                        self.render(lhs, registry, program, current_module_id, writer);
                        writer.emit(" ≥ ");
                        self.render(rhs, registry, program, current_module_id, writer);
                        writer.emit("))");
                    }
                }
            }

            Expression::UnOp { op, operand } => {
                match op {
                    UnOp::Not => {
                        writer.emit("(!");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    UnOp::CastU8 => {
                        writer.emit("(toUInt8 ");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    UnOp::CastU16 => {
                        writer.emit("(toUInt16 ");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    UnOp::CastU32 => {
                        writer.emit("(toUInt32 ");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    UnOp::CastU64 => {
                        writer.emit("(toUInt64 ");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    UnOp::CastU128 => {
                        writer.emit("(toUInt128 ");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    UnOp::CastU256 => {
                        writer.emit("(toUInt256 ");
                        self.render(operand, registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                }
            }

            Expression::Cast { value, target_type } => {
                // Use toUIntXXX conversion functions with dot notation
                // NOTE: This works for primitive types (UInt8.toUInt128 is defined in TypeConversion.lean)
                // For struct types, the IR should have already generated field access before the cast
                use intermediate_theorem_format::TheoremType;
                let func_name = match target_type {
                    TheoremType::UInt(8) => Some("toUInt8"),
                    TheoremType::UInt(16) => Some("toUInt16"),
                    TheoremType::UInt(32) => Some("toUInt32"),
                    TheoremType::UInt(64) => Some("toUInt64"),
                    TheoremType::UInt(128) => Some("toUInt128"),
                    TheoremType::UInt(256) => Some("toUInt256"),
                    _ => None,
                };

                if let Some(func) = func_name {
                    // Use dot notation: value.toUInt128
                    writer.emit("(");
                    self.render(value, registry, program, current_module_id, writer);
                    writer.emit(".");
                    writer.emit(func);
                    writer.emit(")");
                } else {
                    // For non-UInt types, fall back to cast with type annotation
                    writer.emit("(cast ");
                    self.render(value, registry, program, current_module_id, writer);
                    writer.emit(" : ");
                    self.type_renderer.render(target_type, writer);
                    writer.emit(")");
                }
            }

            Expression::Call { function, args, type_args, .. } => {
                // Get function name
                let func_name = if let Some(func) = program.get_function(*function) {
                    // Escape the function name for Lean reserved words
                    let escaped_func_name = escape::escape_identifier(&func.name);

                    // Try to get the module for this function to qualify the call
                    if let Some(module) = program.get_module(func.module_id) {
                        // Check if we're calling a function in the same module
                        if func.module_id == current_module_id {
                            // Same module - use unqualified name
                            escaped_func_name
                        } else {
                            // Cross-module call: use Module.function format
                            // Handle name conflicts like "vector" -> "MoveVector"
                            let capitalized_module = if module.name == "vector" {
                                "MoveVector".to_string()
                            } else {
                                Self::capitalize_first(&module.name)
                            };
                            format!("{}.{}", capitalized_module, escaped_func_name)
                        }
                    } else {
                        // Module not found, use unqualified (escaped)
                        escaped_func_name
                    }
                } else {
                    // Function not found, use placeholder
                    format!("func_{}", function)
                };

                // All Move functions take explicit type parameters
                // Unlike Lean's implicit type inference, Move functions have type params in their signatures
                // So we always pass type args first, then value args
                let has_args = !type_args.is_empty() || !args.is_empty();

                if has_args {
                    writer.emit("(");
                    writer.emit(&func_name);

                    // Render type arguments
                    for ty in type_args {
                        writer.emit(" ");
                        self.type_renderer.render(ty, writer);
                    }

                    // Render value arguments
                    for arg in args {
                        writer.emit(" ");
                        self.render(arg, registry, program, current_module_id, writer);
                    }

                    writer.emit(")");
                } else {
                    writer.emit(&func_name);
                }
            }

            Expression::Pack { struct_id, fields } => {
                let struct_def = program.structs.get(struct_id)
                    .unwrap_or_else(|| panic!("Missing struct definition for struct ID: {}", struct_id));
                let struct_name = escape::escape_struct_name(&struct_def.name);

                writer.emit("(");
                writer.emit(&struct_name);
                writer.emit(".mk");

                for field in fields {
                    writer.emit(" ");
                    self.render(field, registry, program, current_module_id, writer);
                }

                writer.emit(")");
            }

            Expression::FieldAccess { struct_id, field_index, operand } => {
                let struct_def = program.structs.get(struct_id)
                    .unwrap_or_else(|| panic!("Missing struct definition for struct ID: {}", struct_id));
                let struct_name = escape::escape_struct_name(&struct_def.name);
                let field = struct_def.fields.get(*field_index)
                    .unwrap_or_else(|| panic!("Missing field at index {} in struct {}", field_index, struct_def.name));
                let field_name = escape::escape_identifier(&field.name);

                writer.emit("(");
                writer.emit(&struct_name);
                writer.emit(".");
                writer.emit(&field_name);
                writer.emit(" ");
                self.render(operand, registry, program, current_module_id, writer);
                writer.emit(")");
            }

            Expression::Unpack { struct_id, operand } => {
                let struct_def = program.structs.get(struct_id)
                    .unwrap_or_else(|| panic!("Missing struct definition for struct ID: {}", struct_id));
                let struct_name = escape::escape_struct_name(&struct_def.name);

                // Generate tuple of field accesses: ((Struct.field_name op), ...)
                writer.emit("(");
                for (i, field) in struct_def.fields.iter().enumerate() {
                    if i > 0 {
                        writer.emit(", ");
                    }
                    writer.emit("(");
                    writer.emit(&struct_name);
                    writer.emit(".");
                    writer.emit(&escape::escape_identifier(&field.name));
                    writer.emit(" ");
                    self.render(operand, registry, program, current_module_id, writer);
                    writer.emit(")");
                }
                writer.emit(")");
            }

            Expression::VecOp { op, operands } => {
                use intermediate_theorem_format::VectorOp;
                match op {
                    VectorOp::Empty => {
                        writer.emit("List.nil");
                    }
                    VectorOp::Length => {
                        writer.emit("(List.length ");
                        self.render(&operands[0], registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    VectorOp::Push => {
                        writer.emit("(List.concat ");
                        self.render(&operands[0], registry, program, current_module_id, writer);
                        writer.emit(" [");
                        self.render(&operands[1], registry, program, current_module_id, writer);
                        writer.emit("])");
                    }
                    VectorOp::Pop => {
                        writer.emit("(List.dropLast ");
                        self.render(&operands[0], registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    VectorOp::Borrow | VectorOp::BorrowMut => {
                        writer.emit("(List.get! ");
                        self.render(&operands[0], registry, program, current_module_id, writer);
                        writer.emit(" ");
                        self.render(&operands[1], registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                    VectorOp::Swap => {
                        writer.emit("(List.swap ");
                        self.render(&operands[0], registry, program, current_module_id, writer);
                        writer.emit(" ");
                        self.render(&operands[1], registry, program, current_module_id, writer);
                        writer.emit(" ");
                        self.render(&operands[2], registry, program, current_module_id, writer);
                        writer.emit(")");
                    }
                }
            }

            // Tuple expression - render as Lean tuple
            Expression::Tuple(exprs) => {
                if exprs.is_empty() {
                    writer.emit("()");
                } else if exprs.len() == 1 {
                    self.render(&exprs[0], registry, program, current_module_id, writer);
                } else {
                    writer.emit("(");
                    for (i, e) in exprs.iter().enumerate() {
                        self.render(e, registry, program, current_module_id, writer);
                        if i < exprs.len() - 1 {
                            writer.emit(", ");
                        }
                    }
                    writer.emit(")");
                }
            }

            // IfExpr and WhileExpr are handled specially in statement_renderer
            // They should be bound via Let statements, not rendered as pure expressions
            Expression::IfExpr { .. } => {
                // This should be handled by statement_renderer.render_if_expr
                writer.emit("/* IfExpr should be bound via Let */");
            }

            Expression::WhileExpr { .. } => {
                // This should be handled by statement_renderer.render_while_expr
                writer.emit("/* WhileExpr should be bound via Let */");
            }
        }
    }
}
