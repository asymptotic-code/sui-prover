// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Unified IR renderer - renders IR nodes to Lean syntax

use super::context::RenderCtx;
use super::type_renderer::render_type;
use crate::escape;
use intermediate_theorem_format::{BinOp, BitOp, Const, FunctionVariant, IRNode, UnOp};
use std::fmt::Write;

/// Check if a function is a MoveReal operation and transform it for generic specs
/// Transform int_ops calls to built-in Int operations
///
/// Only transforms functions that are actually from the int_ops module and are
/// the runtime/pure variants (not aborts variants which need type-specific handling).
fn try_transform_int_ops_call<W: Write>(
    func_name: &str,
    module_name: &str,
    variant: FunctionVariant,
    args: &[IRNode],
    ctx: &mut RenderCtx<W>,
) -> bool {
    // Only transform if this is actually from the int_ops module
    if !module_name.ends_with("int_ops") {
        return false;
    }

    // Don't transform aborts variants - they need type-specific handling
    // (e.g., I32.abs.aborts instead of Int.abs)
    if variant == FunctionVariant::Aborts {
        return false;
    }

    // Transform int_ops operations to Lean's built-in Int operations
    match func_name {
        // Arithmetic - map to Int operators (built-in)
        "add" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" + ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "sub" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" - ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "mul" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" * ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "abs" => {
            if let Some(arg) = args.first() {
                ctx.write("Int_ops.abs ");
                render_with_parens_if_needed(arg, ctx);
                return true;
            }
        }

        "neg" => {
            if let Some(arg) = args.first() {
                ctx.write("(-");
                render(arg, ctx);
                ctx.write(")");
                return true;
            }
        }

        _ => {}
    }

    false
}

fn try_transform_movereal_call<W: Write>(
    func_name: &str,
    args: &[IRNode],
    ctx: &mut RenderCtx<W>,
) -> bool {
    // Check if we're in a generic spec context
    let generic_spec = match ctx.generic_spec {
        Some(spec) => spec,
        None => return false,
    };

    // Transform MoveReal operations to Real operations and typeclass methods
    match func_name {
        // Conversion from unsigned integers - just cast to Real
        "from_u128" | "from_u64" | "from_u32" | "from_u16" | "from_u8" => {
            if let Some(arg) = args.first() {
                ctx.write("(");
                render(arg, ctx);
                ctx.write(" : ℝ)");
                return true;
            }
        }

        // Conversion from signed integers - use IntegerType.toReal
        "from_i128_bits" | "from_i64_bits" | "from_i32_bits" | "from_i16_bits" | "from_i8_bits" => {
            if let Some(arg) = args.first() {
                ctx.write("IntegerType.toReal ");
                render_with_parens_if_needed(arg, ctx);
                return true;
            }
        }

        // Arithmetic - map to Real operators
        "add" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" + ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "sub" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" - ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "mul" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" * ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "div" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" / ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        "pow" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" ^ ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        // Floor - use NumericType.fromReal with Real.floor
        "floor_u128" | "floor_u64" | "floor_u32" | "floor_u16" | "floor_u8" => {
            if let Some(arg) = args.first() {
                ctx.write("NumericType.fromReal (⌊");
                render(arg, ctx);
                ctx.write("⌋)");
                return true;
            }
        }

        // Ceiling - use NumericType.fromReal with Real.ceil
        "ceil_u128" | "ceil_u64" | "ceil_u32" | "ceil_u16" | "ceil_u8" => {
            if let Some(arg) = args.first() {
                ctx.write("NumericType.fromReal (⌈");
                render(arg, ctx);
                ctx.write("⌉)");
                return true;
            }
        }

        // Fraction - just division
        "from_fraction" => {
            if args.len() == 2 {
                ctx.write("(");
                render(&args[0], ctx);
                ctx.write(" / ");
                render(&args[1], ctx);
                ctx.write(")");
                return true;
            }
        }

        _ => {}
    }

    false
}

/// Render an IR node to Lean syntax
pub fn render<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    match ir {
        // Atomic expressions - always inline
        IRNode::Var(name) => {
            ctx.write(&escape::escape_identifier(name));
        }

        IRNode::Const(c) => render_const(c, ctx),

        IRNode::Tuple(elems) => {
            ctx.tuple(elems.iter(), "()", |ctx, elem| render(elem, ctx));
        }

        IRNode::BinOp { op, lhs, rhs } => {
            // Comparison operators (<, <=, >, >=) return Prop in Lean
            // Logical operators (And, Or) return Prop when using ∧, ∨
            // Equality (==, !=) uses BEq and returns Bool
            //
            // With explicit ToProp/ToBool coercions in the IR, we render
            // operators based on what the IR expects, not context.
            // Comparisons always use Prop operators since that's what Lean provides.
            // ToBool nodes will wrap with `decide` where Bool is needed.
            let op_sym = binop_symbol(*op);

            // Check if rhs needs multi-line rendering (contains Let bindings)
            if needs_multiline(rhs) {
                render_with_parens_if_needed(lhs, ctx);
                ctx.write(op_sym);
                ctx.write("(");
                ctx.indent(true);
                render(rhs, ctx);
                ctx.write(")");
                ctx.dedent(false);
            } else {
                render_with_parens_if_needed(lhs, ctx);
                ctx.write(op_sym);
                render_with_parens_if_needed(rhs, ctx);
            }
        }

        IRNode::UnOp { op, operand } => {
            match op {
                UnOp::Not => {
                    // Use ! for Bool negation (Lean's Bool.not)
                    // For Prop negation, use ToProp around Bool expressions
                    ctx.write("!");
                    render_with_parens_if_needed(operand, ctx);
                }
                UnOp::BitNot => {
                    ctx.write("~~~");
                    render_with_parens_if_needed(operand, ctx);
                }
                UnOp::Cast(bits) => {
                    // Use BoundedNat.convert to explicitly convert between different bounds
                    // Type ascription alone does not work because Lean has no Coe for this
                    ctx.write("(BoundedNat.convert ");
                    render_with_parens_if_needed(operand, ctx);
                    ctx.write(&format!(" : BoundedNat (2^{}))", bits));
                }
            }
        }

        IRNode::Call {
            function,
            args,
            type_args,
        } => {
            let func = ctx.program.functions.get(function);
            let module = ctx.program.modules.get(func.module_id);

            // Try to transform int_ops operations to built-in Int operations
            if try_transform_int_ops_call(&func.name, &module.name, function.variant, args, ctx) {
                return;
            }

            // Try to transform MoveReal operations for generic specs
            if try_transform_movereal_call(&func.name, args, ctx) {
                return;
            }

            // Determine the correct function name
            // With the new architecture:
            // - Impl functions are in Impls/ namespace - just use their names
            // - Spec functions are in Specs/ namespace - use target name if they target something
            let base_id = intermediate_theorem_format::FunctionID::new(function.base);
            let base_func = ctx.program.functions.get(&base_id);

            let base_name = if let Some(target_id) = func.spec_target {
                // This function has a spec_target, meaning it's a spec function or spec variant.
                // For spec variants like .requires or .error_bound, use target name + suffix
                // (they're defined in SpecDefs with target's name)
                // For the spec function itself (Runtime variant), use its OWN name (e.g., xxx_spec)
                let target_func = ctx
                    .program
                    .functions
                    .get(&intermediate_theorem_format::FunctionID::new(target_id));
                let target_name = target_func.name.clone();

                if function.variant.is_spec_variant()
                    && function.variant != FunctionVariant::Runtime
                {
                    // Spec variant (.requires, .error_bound, .ensures) - use target name + suffix
                    match function.variant {
                        FunctionVariant::Ensures(0) => format!("{}.ensures", target_name),
                        FunctionVariant::Ensures(n) => format!("{}.ensures_{}", target_name, n),
                        _ => format!("{}{}", target_name, function.variant.suffix()),
                    }
                } else {
                    // Runtime/Pure variant of a spec function - use the SPEC function's own name
                    // (e.g., get_sqrt_price_at_positive_tick_spec, not get_sqrt_price_at_positive_tick)
                    func.name.clone()
                }
            } else {
                func.full_name(function.variant)
            };

            // Use unqualified name only if we're in the same module AND have a current namespace
            // When current_module_namespace is None (e.g., in Goals), always qualify
            // For spec functions:
            // - Spec variant functions (.requires, .error_bound, etc.) are defined in SpecDefs
            //   with the SPEC module's namespace, so use the spec's module
            // - For Runtime/Pure variants of spec functions, use the SPEC function's own module
            //   (e.g., i128_mul_spec is in Integer_mate_specs, not I128)
            let effective_module_id = if let Some(_target_id) = func.spec_target {
                // Spec functions (with spec_target) are always in their own module
                // This includes both:
                // - Spec variant functions (.requires, .error_bound, .ensures)
                // - The spec function itself (Runtime variant, e.g., i128_mul_spec)
                func.module_id // Use spec's module
            } else {
                func.module_id
            };

            let func_name = if effective_module_id == ctx.current_module_id
                && ctx.current_module_namespace.is_some()
            {
                escape::escape_identifier(&base_name)
            } else {
                let module = ctx.program.modules.get(effective_module_id);
                let namespace = escape::module_name_to_namespace(&module.name);
                format!("{}.{}", namespace, escape::escape_identifier(&base_name))
            };

            // Extract and render any let bindings from arguments first
            // This handles cases where args contain Let nodes which can't be rendered inline
            let mut extracted_args = Vec::new();
            for arg in args {
                let (lets, value) = extract_lets(arg);
                for (pattern, let_value) in lets {
                    ctx.write("let ");
                    ctx.tuple(pattern.iter(), "_", |ctx, p| {
                        ctx.write(&escape::escape_identifier(p))
                    });
                    ctx.write(" := ");
                    render(&let_value, ctx);
                    ctx.newline();
                }
                extracted_args.push(value);
            }

            ctx.write(&func_name);
            for ty in type_args {
                ctx.write(" ");
                render_type(ty, ctx);
            }
            for arg in &extracted_args {
                ctx.write(" ");
                render_with_parens_if_needed(arg, ctx);
            }
        }

        IRNode::Pack {
            struct_id,
            type_args: _, // Type args are implicit in Lean struct constructors
            fields,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let module_def = ctx.program.modules.get(struct_def.module_id);
            let escaped_name = escape::escape_struct_name(&struct_def.name);

            // Qualify struct constructor like we do for types
            let qualified_name = if escape::is_lean_builtin(&struct_def.name) {
                escaped_name
            } else {
                let namespace = escape::module_name_to_namespace(&module_def.name);
                if ctx.current_module_namespace == Some(namespace.as_str()) {
                    escaped_name
                } else {
                    format!("{}.{}", namespace, escaped_name)
                }
            };

            // In Lean 4, struct constructors don't take explicit type arguments
            // The type is inferred from the field values
            ctx.write(&format!("{}.mk", qualified_name));
            for field in fields {
                ctx.write(" ");
                render_with_parens_if_needed(field, ctx);
            }
        }

        IRNode::Field {
            struct_id,
            field_index,
            base,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let field_name = &struct_def.fields[*field_index].name;

            // Qualify struct name with namespace if different from current module
            let escaped_name = escape::escape_struct_name(&struct_def.name);
            let module_def = ctx.program.modules.get(struct_def.module_id);
            let qualified_name = if struct_def.module_id == ctx.current_module_id {
                escaped_name
            } else {
                let namespace = escape::module_name_to_namespace(&module_def.name);
                format!("{}.{}", namespace, escaped_name)
            };

            ctx.write(&format!(
                "{}.{} ",
                qualified_name,
                escape::escape_identifier(field_name)
            ));
            render_with_parens_if_needed(base, ctx);
        }

        IRNode::Unpack { struct_id, value } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let struct_name = escape::escape_struct_name(&struct_def.name);
            ctx.write("(");
            ctx.sep_with(", ", struct_def.fields.iter(), |ctx, field| {
                ctx.write(&struct_name);
                ctx.write(".");
                ctx.write(&escape::escape_identifier(&field.name));
                ctx.write(" ");
                render_with_parens_if_needed(value, ctx);
            });
            ctx.write(")");
        }

        IRNode::UpdateField {
            base,
            struct_id,
            field_index,
            value,
        } => {
            let struct_def = ctx.program.structs.get(*struct_id);
            let field_name = &struct_def.fields[*field_index].name;
            ctx.write("{ ");
            render(base, ctx);
            ctx.write(&format!(" with {} := ", field_name));
            render(value, ctx);
            ctx.write(" }");
        }

        IRNode::UpdateVec { base, index, value } => {
            render(base, ctx);
            ctx.write(".set ");
            render_with_parens_if_needed(index, ctx);
            ctx.write(" ");
            render_with_parens_if_needed(value, ctx);
        }

        // Non-atomic expressions - multi-line
        IRNode::Let { pattern, value } => {
            // If the value is a Let or Block containing Lets, we need to extract them
            // to avoid malformed Lean syntax like `let x := let y := v`
            let (extracted_lets, final_value) = extract_lets(value);

            // Render extracted lets first
            for (inner_pattern, inner_value) in extracted_lets {
                ctx.write("let ");
                ctx.tuple(inner_pattern.iter(), "_", |ctx, p| {
                    ctx.write(&escape::escape_identifier(p))
                });
                ctx.write(" := ");
                render(&inner_value, ctx);
                ctx.newline();
            }

            // Now render the main let with the final value
            ctx.write("let ");
            ctx.tuple(pattern.iter(), "_", |ctx, p| {
                ctx.write(&escape::escape_identifier(p))
            });
            ctx.write(" := ");
            render(&final_value, ctx);
        }

        IRNode::Block { children } => {
            // Filter out Requires/Ensures nodes which render as empty
            // Also filter out bare Var nodes in non-last position (invalid Lean syntax)
            let filtered: Vec<_> = children
                .iter()
                .filter(|c| !matches!(c, IRNode::Requires(_) | IRNode::Ensures(_)))
                .collect();

            for (i, child) in filtered.iter().enumerate() {
                let is_last = i == filtered.len() - 1;
                // Skip bare Var or Tuple expressions that aren't the last element
                // (these are invalid in let sequences - only last element can be a bare expression)
                if !is_last && is_bare_value_expression(child) {
                    continue;
                }
                render(child, ctx);
                if !is_last {
                    ctx.newline();
                }
            }
        }

        IRNode::If {
            cond,
            then_branch,
            else_branch,
        } => {
            ctx.write("if ");
            render(cond, ctx);
            ctx.write(" then");
            ctx.indent(true);
            render(then_branch, ctx);
            // If branch ends with Let, add () to return unit
            if matches!(**then_branch, IRNode::Let { .. }) {
                ctx.newline();
                ctx.write("()");
            }
            ctx.dedent(false);
            ctx.newline();
            ctx.write("else");
            ctx.indent(true);
            render(else_branch, ctx);
            // If branch ends with Let, add () to return unit
            if matches!(**else_branch, IRNode::Let { .. }) {
                ctx.newline();
                ctx.write("()");
            }
            ctx.dedent(false);
        }

        IRNode::While {
            cond, body, vars, ..
        } => {
            if vars.is_empty() {
                // Unit state - use _ pattern and don't return state tuple
                ctx.write("whileLoopPure (fun _ =>");
                ctx.indent(true);
                render(cond, ctx);
                ctx.dedent(false);
                ctx.newline();
                ctx.write(") (fun _ =>");
                ctx.indent(true);
                render(body, ctx);
                // Body needs to return () for unit state loops, but only if it doesn't already
                // (e.g., If with Let branches already returns unit)
                if !body_returns_unit(body) {
                    ctx.newline();
                    ctx.write("()");
                }
                ctx.dedent(false);
                ctx.newline();
                ctx.write(") ()");
            } else {
                // Use whileLoopPure for all loops with state
                let escaped_vars: Vec<String> =
                    vars.iter().map(|v| escape::escape_identifier(v)).collect();
                let vars_str = escaped_vars.join(", ");
                ctx.write(&format!("whileLoopPure (fun ({}) =>", vars_str));
                ctx.indent(true);
                render(cond, ctx);
                ctx.dedent(false);
                ctx.newline();
                ctx.write(&format!(") (fun ({}) =>", vars_str));
                ctx.indent(true);
                render(body, ctx);
                // Body should end with the return state tuple
                // If it ends with a Let, we need to append the state tuple
                if body_ends_with_let(body) {
                    ctx.newline();
                    ctx.write(&format!("({})", vars_str));
                }
                ctx.dedent(false);
                ctx.newline();
                ctx.write(&format!(") ({})", vars_str));
            }
        }

        IRNode::WhileAborts {
            cond,
            body_aborts,
            body_pure,
            vars,
            ..
        } => {
            // whileLoopAborts (fun vars => cond) (fun vars => body_aborts) (fun vars => body_pure; vars) init
            if vars.is_empty() {
                // Unit state - use _ pattern
                ctx.write("whileLoopAborts (fun _ =>");
                ctx.indent(true);
                render(cond, ctx);
                ctx.dedent(false);
                ctx.newline();

                ctx.write(") (fun _ =>");
                ctx.indent(true);
                render(body_aborts, ctx);
                // Body_aborts returns Bool/Prop, but we still need proper lambda return
                // If body ends with Let, add False to return (no abort from this iteration check)
                ctx.newline();
                ctx.write("False");
                ctx.dedent(false);
                ctx.newline();

                ctx.write(") (fun _ =>");
                ctx.indent(true);
                render(body_pure, ctx);
                // Body needs to return () for unit state loops
                ctx.newline();
                ctx.write("()");
                ctx.dedent(false);
                ctx.newline();

                ctx.write(") ()");
            } else {
                let escaped_vars: Vec<String> =
                    vars.iter().map(|v| escape::escape_identifier(v)).collect();
                let vars_str = escaped_vars.join(", ");

                ctx.write(&format!("whileLoopAborts (fun ({}) =>", vars_str));
                ctx.indent(true);
                render(cond, ctx);
                ctx.dedent(false);
                ctx.newline();

                ctx.write(&format!(") (fun ({}) =>", vars_str));
                ctx.indent(true);
                render(body_aborts, ctx);
                ctx.dedent(false);
                ctx.newline();

                ctx.write(&format!(") (fun ({}) =>", vars_str));
                ctx.indent(true);
                render(body_pure, ctx);
                // Body_pure now includes the return tuple, so don't append it here
                ctx.dedent(false);
                ctx.newline();

                ctx.write(&format!(") ({})", vars_str));
            }
        }

        IRNode::Return(values) => {
            ctx.tuple(values.iter(), "()", |ctx, v| render(v, ctx));
        }

        IRNode::Abort(code) => {
            // Abort nodes should not appear in pure code - they are filtered out
            // during the Pure variant generation. If we hit this, something is wrong.
            panic!(
                "BUG: Abort node {:?} encountered during Lean rendering. \
                Abort nodes should be stripped before rendering. \
                This indicates a bug in the rendering pipeline - \
                functions with aborts should not be rendered directly.",
                code
            );
        }

        IRNode::Requires(_)
        | IRNode::Ensures(_)
        | IRNode::ErrorBound(_)
        | IRNode::ErrorBoundRelative { .. }
        | IRNode::ErrorBoundGoal { .. } => {
            // Spec nodes should be stripped before rendering
        }

        IRNode::BitOp(bit_op) => {
            match bit_op {
                BitOp::Extract { high, low, operand } => {
                    // Extract bits by shifting right and masking
                    // (operand >>> low) &&& ((1 <<< (high - low + 1)) - 1)
                    let width = high - low + 1;
                    ctx.write("((");
                    render_with_parens_if_needed(operand, ctx);
                    // Use UInt8 for shift amount to satisfy Lean's type requirements
                    ctx.write(&format!(") >>> ({} : UInt8))", low));
                    if width < 32 {
                        // Mask to extract only the relevant bits
                        let mask = (1u64 << width) - 1;
                        ctx.write(&format!(" &&& {}", mask));
                    }
                }
                BitOp::Concat { high, low } => {
                    // Concat: (high <<< low_width) ||| low
                    // For now, just render as a tuple representation
                    ctx.write("(");
                    render_with_parens_if_needed(high, ctx);
                    ctx.write(", ");
                    render_with_parens_if_needed(low, ctx);
                    ctx.write(")");
                }
                BitOp::ZeroExtend { operand, .. } => {
                    // Zero extension is implicit in Lean's type coercion
                    render_with_parens_if_needed(operand, ctx);
                }
                BitOp::SignExtend { operand, .. } => {
                    // Sign extension needs explicit handling
                    // For now, just render the operand
                    render_with_parens_if_needed(operand, ctx);
                }
            }
        }

        IRNode::Pure(inner) => {
            // Lift a pure value into Except: pure (expr)
            ctx.write("pure (");
            render(inner, ctx);
            ctx.write(")");
        }

        IRNode::ToProp(inner) => {
            // Convert Bool to Prop: (expr = true)
            // This lifts a computational boolean to a logical proposition
            // Need parens around inner to handle cases like (a != b) = true
            ctx.write("(");
            render_with_parens_if_needed(inner, ctx);
            ctx.write(" = true)");
        }

        IRNode::ToBool(inner) => {
            // Convert Prop to Bool: decide expr
            // Requires Decidable instance for the proposition
            ctx.write("(decide ");
            render_with_parens_if_needed(inner, ctx);
            ctx.write(")");
        }
    }
}

fn render_with_parens_if_needed<W: Write>(ir: &IRNode, ctx: &mut RenderCtx<W>) {
    if ir.is_atomic() {
        render(ir, ctx);
    } else {
        ctx.write("(");
        render(ir, ctx);
        ctx.write(")");
    }
}

/// Extract Let bindings from an IR node, returning the extracted lets and the remaining expression.
/// This is used to hoist let bindings out of argument positions where they can't be rendered inline.
fn extract_lets(ir: &IRNode) -> (Vec<(Vec<String>, IRNode)>, IRNode) {
    match ir {
        IRNode::Let { pattern, value } => {
            // Check if the value itself has lets to extract
            let (inner_lets, inner_value) = extract_lets(value);
            let mut lets = inner_lets;
            lets.push((pattern.clone(), inner_value));
            // Return the pattern variable(s) as a Var reference
            if pattern.len() == 1 {
                (lets, IRNode::Var(pattern[0].clone()))
            } else {
                // For tuple patterns, wrap in a tuple
                (
                    lets,
                    IRNode::Tuple(pattern.iter().map(|p| IRNode::Var(p.clone())).collect()),
                )
            }
        }
        IRNode::Block { children } if !children.is_empty() => {
            // For blocks, extract lets from all children except the last
            // and return the last as the value
            let mut lets = Vec::new();
            for (i, child) in children.iter().enumerate() {
                if i < children.len() - 1 {
                    // This should be a Let or something that can be extracted
                    let (child_lets, _) = extract_lets(child);
                    lets.extend(child_lets);
                } else {
                    // Last element is the result
                    let (last_lets, last_value) = extract_lets(child);
                    lets.extend(last_lets);
                    return (lets, last_value);
                }
            }
            (lets, ir.clone())
        }
        // For other nodes, no extraction needed
        _ => (Vec::new(), ir.clone()),
    }
}

/// Check if a node is a bare value expression that doesn't produce a Let binding.
/// These are invalid in non-last position of a let sequence.
fn is_bare_value_expression(ir: &IRNode) -> bool {
    match ir {
        IRNode::Var(_) | IRNode::Const(_) | IRNode::Tuple(_) => true,
        IRNode::BinOp { .. } | IRNode::UnOp { .. } => true,
        // Don't skip Call - they might have side effects
        _ => false,
    }
}

/// Check if an expression needs multi-line rendering.
/// This is true for expressions containing Let bindings or multi-statement Blocks.
fn needs_multiline(ir: &IRNode) -> bool {
    match ir {
        IRNode::Let { .. } => true,
        IRNode::Block { children } => {
            // Filter out empty Requires/Ensures
            let filtered: Vec<_> = children
                .iter()
                .filter(|c| !matches!(c, IRNode::Requires(_) | IRNode::Ensures(_)))
                .collect();
            filtered.len() > 1 || filtered.iter().any(|c| needs_multiline(c))
        }
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => needs_multiline(then_branch) || needs_multiline(else_branch),
        IRNode::BinOp { lhs, rhs, .. } => needs_multiline(lhs) || needs_multiline(rhs),
        _ => false,
    }
}

fn render_const<W: Write>(c: &Const, ctx: &mut RenderCtx<W>) {
    match c {
        Const::Bool(b) => {
            // Bool constants use lowercase true/false
            // For Prop constants, the IR should use ToProp(Const::Bool(...))
            ctx.write(if *b { "true" } else { "false" })
        }
        Const::UInt { bits, value } => {
            if *bits == 8 || *bits == 128 {
                ctx.write(&format!("({} : BoundedNat (2^{}))", value, bits));
            } else {
                ctx.write(&value.to_string());
            }
        }
        Const::Address(addr) => ctx.write(&addr.to_string()),
        Const::Vector { elems, .. } => {
            ctx.write("[");
            for (i, e) in elems.iter().enumerate() {
                if i > 0 {
                    ctx.write(", ");
                }
                render_const(e, ctx);
            }
            ctx.write("]");
        }
    }
}

/// Get the symbol for a binary operator.
/// With explicit ToProp/ToBool coercions in the IR:
/// - Comparisons (<, <=, >, >=) use Prop symbols since they inherently return Prop in Lean
/// - Equality (==, !=) uses Bool symbols (BEq typeclass)
/// - Logical operators (And, Or) use Prop symbols (∧, ∨) - we convert at boundaries with ToProp/ToBool
/// - Arithmetic uses standard symbols
fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::Div => " / ",
        BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ",
        BinOp::BitOr => " ||| ",
        BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ",
        BinOp::Shr => " >>> ",
        // Logical operators use Prop symbols - ToBool wraps when Bool needed
        BinOp::And => " ∧ ",
        BinOp::Or => " ∨ ",
        // Equality uses BEq typeclass which returns Bool
        BinOp::Eq => " == ",
        BinOp::Neq => " != ",
        // Comparisons return Prop in Lean (via DecidableRel)
        BinOp::Lt => " < ",
        BinOp::Le => " ≤ ",
        BinOp::Gt => " > ",
        BinOp::Ge => " ≥ ",
    }
}

/// Bool-returning operators for use in runtime code
fn binop_symbol_bool(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::Div => " / ",
        BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ",
        BinOp::BitOr => " ||| ",
        BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ",
        BinOp::Shr => " >>> ",
        BinOp::And => " && ",
        BinOp::Or => " || ",
        BinOp::Eq => " == ",
        BinOp::Neq => " != ",
        BinOp::Lt => " < ",
        BinOp::Le => " <= ",
        BinOp::Gt => " > ",
        BinOp::Ge => " >= ",
    }
}

/// Prop-returning operators for use in .aborts functions
fn binop_symbol_prop(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => " + ",
        BinOp::Sub => " - ",
        BinOp::Mul => " * ",
        BinOp::Div => " / ",
        BinOp::Mod => " % ",
        BinOp::BitAnd => " &&& ",
        BinOp::BitOr => " ||| ",
        BinOp::BitXor => " ^^^ ",
        BinOp::Shl => " <<< ",
        BinOp::Shr => " >>> ",
        BinOp::And => " ∧ ",
        BinOp::Or => " ∨ ",
        BinOp::Eq => " = ",
        BinOp::Neq => " ≠ ",
        BinOp::Lt => " < ",
        BinOp::Le => " ≤ ",
        BinOp::Gt => " > ",
        BinOp::Ge => " ≥ ",
    }
}

fn bounded_nat_type(bits: usize) -> String {
    format!("BoundedNat (2^{})", bits)
}

/// Check if an IR node returns unit ().
/// This checks if the node already produces () so we don't add duplicate returns.
fn body_returns_unit(ir: &IRNode) -> bool {
    match ir {
        // If with Let branches - we add () to each branch, so the if returns unit
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => {
            matches!(**then_branch, IRNode::Let { .. })
                && matches!(**else_branch, IRNode::Let { .. })
        }
        // Block returns unit if its last child does
        IRNode::Block { children } => children
            .last()
            .is_some_and(body_returns_unit),
        _ => false,
    }
}

/// Check if a loop body ends with a Let binding (needs state tuple appended)
fn body_ends_with_let(ir: &IRNode) -> bool {
    match ir {
        IRNode::Let { .. } => true,
        IRNode::Block { children } => children
            .last()
            .is_some_and(body_ends_with_let),
        IRNode::If {
            then_branch,
            else_branch,
            ..
        } => body_ends_with_let(then_branch) || body_ends_with_let(else_branch),
        _ => false,
    }
}
