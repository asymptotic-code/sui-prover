// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Simplification and analysis of abort predicates using Z3

use super::translate::{new_context, SmtContext};
use crate::data::functions::{Function, FunctionVariant};
use crate::data::Program;
use crate::{BinOp, BitOp, Const, FunctionID, IRNode, Type, UnOp};
use ethnum::U256;
use std::collections::HashMap;
use z3::{SatResult, Solver};

/// Result of analyzing an abort predicate
#[derive(Debug, Clone)]
pub enum AbortAnalysisResult {
    /// The function never aborts (predicate is always false)
    NeverAborts,
    /// The function always aborts (predicate is always true)
    AlwaysAborts,
    /// The function may abort depending on inputs, with simplified IR and string representation
    MayAbort {
        /// Simplified IR expression for the abort condition
        simplified_ir: IRNode,
        /// Human-readable string representation
        condition_str: String,
    },
    /// Could not analyze (contains unsupported constructs)
    Unknown,
}

impl AbortAnalysisResult {
    /// Check if this is the MayAbort variant (regardless of condition)
    pub fn is_conditional(&self) -> bool {
        matches!(self, AbortAnalysisResult::MayAbort { .. })
    }

    /// Get the simplified condition string, if available
    pub fn condition(&self) -> Option<&str> {
        match self {
            AbortAnalysisResult::MayAbort { condition_str, .. } => Some(condition_str),
            _ => None,
        }
    }

    /// Get the simplified IR, if available
    pub fn simplified_ir(&self) -> Option<&IRNode> {
        match self {
            AbortAnalysisResult::MayAbort { simplified_ir, .. } => Some(simplified_ir),
            _ => None,
        }
    }
}

/// Analyze abort predicates for all .aborts functions in the program.
/// Returns a map from function base ID to analysis result.
pub fn simplify_aborts(program: &Program) -> Vec<(FunctionID, AbortAnalysisResult)> {
    let ctx = new_context();
    let mut results = Vec::new();

    for (func_id, func) in program.functions.iter() {
        // Only analyze .aborts variants
        if func_id.variant != FunctionVariant::Aborts {
            continue;
        }

        let result = analyze_abort_body(&ctx, program, func);
        log::info!(
            "Abort analysis for {}: {:?}",
            func.name,
            result
        );
        results.push((func_id, result));
    }

    results
}

/// Analyze a single abort function body
fn analyze_abort_body(ctx: &z3::Context, program: &Program, func: &Function) -> AbortAnalysisResult {
    let mut smt_ctx = SmtContext::with_program(ctx, program);

    // Build a mapping from Z3 variable names to parameter info
    let mut var_types: HashMap<String, Type> = HashMap::new();

    // Create symbolic variables for all parameters
    for param in &func.signature.parameters {
        if let Some(var) = smt_ctx.fresh_for_type(&param.name, &param.param_type) {
            smt_ctx.bind_var(param.name.clone(), var);
            var_types.insert(param.name.clone(), param.param_type.clone());
        } else {
            log::debug!("Unsupported param type for {}: {:?}", param.name, param.param_type);
            // If we can't create a symbolic var for a param, return Unknown
            eprintln!("  [SMT] {} - skipping: unsupported param type {:?}", func.name, param.param_type);
            return AbortAnalysisResult::Unknown;
        }
    }

    // Translate the function body to Z3
    let Some(z3_expr) = smt_ctx.translate_to_bool(&func.body) else {
        log::debug!("Failed to translate {} to Z3", func.name);
        eprintln!("  [SMT] {} - skipping: failed to translate body", func.name);
        return AbortAnalysisResult::Unknown;
    };


    // Check if always false (never aborts)
    let solver = Solver::new(ctx);
    solver.assert(&z3_expr);
    match solver.check() {
        SatResult::Unsat => return AbortAnalysisResult::NeverAborts,
        SatResult::Unknown => return AbortAnalysisResult::Unknown,
        SatResult::Sat => {}
    }

    // Check if always true (always aborts)
    let solver = Solver::new(ctx);
    solver.assert(&z3_expr.not());
    match solver.check() {
        SatResult::Unsat => return AbortAnalysisResult::AlwaysAborts,
        SatResult::Unknown => return AbortAnalysisResult::Unknown,
        SatResult::Sat => {}
    }

    // Return the function body directly - simplification happens in the optimize pass
    // after variant generation, which gives us DCE benefits too
    AbortAnalysisResult::MayAbort {
        simplified_ir: func.body.clone(),
        condition_str: format!("{:?}", func.body),
    }
}

/// Convert a Z3 Bool AST back to IRNode
fn z3_to_ir(
    expr: &z3::ast::Bool,
    var_types: &HashMap<String, Type>,
    var_to_ir: &HashMap<String, IRNode>,
) -> Option<IRNode> {
    let expr_str = expr.to_string();

    // Check for constants
    if expr_str == "true" {
        return Some(IRNode::Const(Const::Bool(true)));
    }
    if expr_str == "false" {
        return Some(IRNode::Const(Const::Bool(false)));
    }

    // Parse the S-expression
    parse_sexp(&expr_str, var_types, var_to_ir)
}

/// Parse an S-expression string into IRNode
fn parse_sexp(
    s: &str,
    var_types: &HashMap<String, Type>,
    var_to_ir: &HashMap<String, IRNode>,
) -> Option<IRNode> {
    let s = s.trim();

    // Handle constants
    if s == "true" {
        return Some(IRNode::Const(Const::Bool(true)));
    }
    if s == "false" {
        return Some(IRNode::Const(Const::Bool(false)));
    }

    // Handle hex/binary literals
    if s.starts_with("#x") {
        let hex = &s[2..];
        let bits = (hex.len() * 4) as usize;
        if let Ok(value) = U256::from_str_radix(hex, 16) {
            return Some(IRNode::Const(Const::UInt { value, bits }));
        }
    }
    if s.starts_with("#b") {
        let bin = &s[2..];
        let bits = bin.len();
        if let Ok(value) = U256::from_str_radix(bin, 2) {
            return Some(IRNode::Const(Const::UInt { value, bits }));
        }
    }

    // Handle decimal numbers
    if let Ok(value) = s.parse::<u64>() {
        return Some(IRNode::Const(Const::UInt { value: U256::from(value), bits: 64 }));
    }

    // Handle variables (identifiers)
    if !s.starts_with('(') && !s.contains(' ') {
        // Check if this is a mapped variable (like "num1_bits" -> Field access)
        // Recursively resolve until we get to a non-Var or an unmapped Var
        return Some(resolve_var(s, var_to_ir));
    }

    // Handle S-expressions: (op arg1 arg2 ...)
    if !s.starts_with('(') || !s.ends_with(')') {
        return None;
    }

    let inner = &s[1..s.len() - 1];
    let parts = split_sexp(inner);
    if parts.is_empty() {
        return None;
    }

    let op = &parts[0];

    // Handle unary operators
    match op.as_str() {
        "not" if parts.len() == 2 => {
            let operand = parse_sexp(&parts[1], var_types, var_to_ir)?;
            return Some(IRNode::UnOp {
                op: UnOp::Not,
                operand: Box::new(operand),
            });
        }
        "bvnot" if parts.len() == 2 => {
            let operand = parse_sexp(&parts[1], var_types, var_to_ir)?;
            return Some(IRNode::UnOp {
                op: UnOp::BitNot,
                operand: Box::new(operand),
            });
        }
        _ => {}
    }

    // Handle binary operators
    if parts.len() >= 3 {
        let bin_op = match op.as_str() {
            "and" => Some(BinOp::And),
            "or" => Some(BinOp::Or),
            "=" => Some(BinOp::Eq),
            "bvult" => Some(BinOp::Lt),
            "bvule" => Some(BinOp::Le),
            "bvugt" => Some(BinOp::Gt),
            "bvuge" => Some(BinOp::Ge),
            "bvadd" => Some(BinOp::Add),
            "bvsub" => Some(BinOp::Sub),
            "bvmul" => Some(BinOp::Mul),
            "bvudiv" => Some(BinOp::Div),
            "bvurem" => Some(BinOp::Mod),
            "bvand" => Some(BinOp::BitAnd),
            "bvor" => Some(BinOp::BitOr),
            "bvxor" => Some(BinOp::BitXor),
            "bvshl" => Some(BinOp::Shl),
            "bvlshr" => Some(BinOp::Shr),
            _ => None,
        };

        if let Some(bin_op) = bin_op {
            // Handle binary and n-ary operators by chaining
            // All associative operators (and, or, bvand, bvor, bvxor, add, mul) can be n-ary
            if parts.len() >= 3 {
                let mut result = parse_sexp(&parts[1], var_types, var_to_ir)?;
                for part in &parts[2..] {
                    let rhs = parse_sexp(part, var_types, var_to_ir)?;
                    result = IRNode::BinOp {
                        op: bin_op,
                        lhs: Box::new(result),
                        rhs: Box::new(rhs),
                    };
                }
                return Some(result);
            }
        }
    }

    // Handle ite (if-then-else)
    if op == "ite" && parts.len() == 4 {
        let cond = parse_sexp(&parts[1], var_types, var_to_ir)?;
        let then_branch = parse_sexp(&parts[2], var_types, var_to_ir)?;
        let else_branch = parse_sexp(&parts[3], var_types, var_to_ir)?;
        return Some(IRNode::If {
            cond: Box::new(cond),
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
        });
    }

    // Handle extract: ((_ extract hi lo) expr)
    // The "_" is parsed as op, "extract" as parts[1], etc.
    if op == "_" && parts.len() >= 3 && parts[1] == "extract" {
        // This is just the extract spec without the operand
        // We need to look for a wrapper expression
        return None;
    }

    // Handle ((_ extract hi lo) expr) - when parsed as whole expression
    if op.starts_with("(_ extract") {
        // Parse out the hi and lo from the op string
        let extract_parts: Vec<&str> = op.split_whitespace().collect();
        if extract_parts.len() >= 4 {
            // extract_parts[0] = "(_", [1] = "extract", [2] = hi, [3] = lo with trailing ")"
            let hi_str = extract_parts[2];
            let lo_str = extract_parts[3].trim_end_matches(')');
            if let (Ok(high), Ok(low)) = (hi_str.parse::<u32>(), lo_str.parse::<u32>()) {
                if parts.len() >= 2 {
                    let operand = parse_sexp(&parts[1], var_types, var_to_ir)?;
                    return Some(IRNode::BitOp(BitOp::Extract {
                        high,
                        low,
                        operand: Box::new(operand),
                    }));
                }
            }
        }
    }

    // Handle concat
    if op == "concat" {
        if parts.len() == 3 {
            let high = parse_sexp(&parts[1], var_types, var_to_ir)?;
            let low = parse_sexp(&parts[2], var_types, var_to_ir)?;
            return Some(IRNode::BitOp(BitOp::Concat {
                high: Box::new(high),
                low: Box::new(low),
            }));
        } else if parts.len() > 3 {
            // Multiple concats - chain them
            let mut result = parse_sexp(&parts[parts.len() - 1], var_types, var_to_ir)?;
            for i in (1..parts.len() - 1).rev() {
                let high = parse_sexp(&parts[i], var_types, var_to_ir)?;
                result = IRNode::BitOp(BitOp::Concat {
                    high: Box::new(high),
                    low: Box::new(result),
                });
            }
            return Some(result);
        }
    }

    // Handle zero_extend: ((_ zero_extend n) expr)
    if op.starts_with("(_ zero_extend") {
        let extend_parts: Vec<&str> = op.split_whitespace().collect();
        if extend_parts.len() >= 3 {
            let bits_str = extend_parts[2].trim_end_matches(')');
            if let Ok(bits) = bits_str.parse::<u32>() {
                if parts.len() >= 2 {
                    let operand = parse_sexp(&parts[1], var_types, var_to_ir)?;
                    return Some(IRNode::BitOp(BitOp::ZeroExtend {
                        bits,
                        operand: Box::new(operand),
                    }));
                }
            }
        }
    }

    // Handle sign_extend: ((_ sign_extend n) expr)
    if op.starts_with("(_ sign_extend") {
        let extend_parts: Vec<&str> = op.split_whitespace().collect();
        if extend_parts.len() >= 3 {
            let bits_str = extend_parts[2].trim_end_matches(')');
            if let Ok(bits) = bits_str.parse::<u32>() {
                if parts.len() >= 2 {
                    let operand = parse_sexp(&parts[1], var_types, var_to_ir)?;
                    return Some(IRNode::BitOp(BitOp::SignExtend {
                        bits,
                        operand: Box::new(operand),
                    }));
                }
            }
        }
    }

    // Unknown operator
    log::debug!("Unknown S-exp operator '{}' (parts={:?})", op, parts);
    None
}

/// Recursively resolve a variable name to its IR expression.
/// If the variable maps to another Var, keep resolving until we hit
/// a non-Var expression or an unmapped variable.
fn resolve_var(name: &str, var_to_ir: &HashMap<String, IRNode>) -> IRNode {
    let mut current = name;
    let mut seen = std::collections::HashSet::new();

    loop {
        if !seen.insert(current.to_string()) {
            // Cycle detected, stop - return current variable as a leaf
            return IRNode::Var(current.to_string());
        }

        if let Some(ir_expr) = var_to_ir.get(current) {
            match ir_expr {
                IRNode::Var(next_name) => {
                    // Keep resolving
                    current = next_name;
                }
                other => {
                    // Found a non-Var expression, return it
                    // But we also need to recursively resolve any Var nodes inside it
                    return resolve_ir_vars(other.clone(), var_to_ir);
                }
            }
        } else {
            // Unmapped variable - this is a function parameter or unknown
            return IRNode::Var(current.to_string());
        }
    }
}

/// Recursively resolve all Var nodes in an IR expression
fn resolve_ir_vars(ir: IRNode, var_to_ir: &HashMap<String, IRNode>) -> IRNode {
    match ir {
        IRNode::Var(name) => resolve_var(&name, var_to_ir),
        IRNode::BinOp { op, lhs, rhs } => IRNode::BinOp {
            op,
            lhs: Box::new(resolve_ir_vars(*lhs, var_to_ir)),
            rhs: Box::new(resolve_ir_vars(*rhs, var_to_ir)),
        },
        IRNode::UnOp { op, operand } => IRNode::UnOp {
            op,
            operand: Box::new(resolve_ir_vars(*operand, var_to_ir)),
        },
        IRNode::If { cond, then_branch, else_branch } => IRNode::If {
            cond: Box::new(resolve_ir_vars(*cond, var_to_ir)),
            then_branch: Box::new(resolve_ir_vars(*then_branch, var_to_ir)),
            else_branch: Box::new(resolve_ir_vars(*else_branch, var_to_ir)),
        },
        IRNode::Field { struct_id, field_index, base } => IRNode::Field {
            struct_id,
            field_index,
            base: Box::new(resolve_ir_vars(*base, var_to_ir)),
        },
        IRNode::Call { function, args, type_args } => IRNode::Call {
            function,
            args: args.into_iter().map(|a| resolve_ir_vars(a, var_to_ir)).collect(),
            type_args,
        },
        IRNode::BitOp(bit_op) => IRNode::BitOp(match bit_op {
            BitOp::Extract { high, low, operand } => BitOp::Extract {
                high,
                low,
                operand: Box::new(resolve_ir_vars(*operand, var_to_ir)),
            },
            BitOp::Concat { high, low } => BitOp::Concat {
                high: Box::new(resolve_ir_vars(*high, var_to_ir)),
                low: Box::new(resolve_ir_vars(*low, var_to_ir)),
            },
            BitOp::ZeroExtend { bits, operand } => BitOp::ZeroExtend {
                bits,
                operand: Box::new(resolve_ir_vars(*operand, var_to_ir)),
            },
            BitOp::SignExtend { bits, operand } => BitOp::SignExtend {
                bits,
                operand: Box::new(resolve_ir_vars(*operand, var_to_ir)),
            },
        }),
        // For nodes that don't contain sub-expressions, return as-is
        IRNode::Const(_) => ir,
        IRNode::Tuple(elems) => IRNode::Tuple(
            elems.into_iter().map(|e| resolve_ir_vars(e, var_to_ir)).collect()
        ),
        // The rest shouldn't appear in abort conditions, but handle them anyway
        other => other,
    }
}

/// Split an S-expression into top-level parts, respecting parentheses
fn split_sexp(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for c in s.chars() {
        match c {
            '(' => {
                depth += 1;
                current.push(c);
            }
            ')' => {
                depth -= 1;
                current.push(c);
            }
            ' ' | '\n' | '\t' if depth == 0 => {
                if !current.is_empty() {
                    parts.push(current.clone());
                    current.clear();
                }
            }
            _ => {
                current.push(c);
            }
        }
    }

    if !current.is_empty() {
        parts.push(current);
    }

    parts
}

/// Format a Z3 expression string as Lean syntax
fn format_z3_expr_as_lean(z3_str: &str, params: &[crate::data::functions::Parameter]) -> String {
    let mut result = z3_str.to_string();

    // Replace Z3 operators with Lean operators
    result = result.replace("bvult", "<");
    result = result.replace("bvugt", ">");
    result = result.replace("bvule", "≤");
    result = result.replace("bvuge", "≥");
    result = result.replace("bvadd", "+");
    result = result.replace("bvsub", "-");
    result = result.replace("bvmul", "*");
    result = result.replace("bvudiv", "/");
    result = result.replace("bvurem", "%");
    result = result.replace("bvand", "&&&");
    result = result.replace("bvor", "|||");
    result = result.replace("bvxor", "^^^");
    result = result.replace("bvshl", "<<<");
    result = result.replace("bvlshr", ">>>");
    result = result.replace("bvnot", "~~~");
    result = result.replace("not ", "¬");
    result = result.replace("and", "∧");
    result = result.replace("or", "∨");

    // Replace #x hex literals with decimal
    let mut i = 0;
    let chars: Vec<char> = result.chars().collect();
    let mut new_result = String::new();
    while i < chars.len() {
        if i + 1 < chars.len() && chars[i] == '#' && chars[i + 1] == 'x' {
            // Found hex literal, parse it
            let mut hex_str = String::new();
            let mut j = i + 2;
            while j < chars.len() && chars[j].is_ascii_hexdigit() {
                hex_str.push(chars[j]);
                j += 1;
            }
            if let Ok(value) = u128::from_str_radix(&hex_str, 16) {
                new_result.push_str(&format!("{}", value));
            } else {
                new_result.push_str(&format!("#x{}", hex_str));
            }
            i = j;
        } else if i + 1 < chars.len() && chars[i] == '#' && chars[i + 1] == 'b' {
            // Found binary literal, parse it
            let mut bin_str = String::new();
            let mut j = i + 2;
            while j < chars.len() && (chars[j] == '0' || chars[j] == '1') {
                bin_str.push(chars[j]);
                j += 1;
            }
            if let Ok(value) = u128::from_str_radix(&bin_str, 2) {
                new_result.push_str(&format!("{}", value));
            } else {
                new_result.push_str(&format!("#b{}", bin_str));
            }
            i = j;
        } else {
            new_result.push(chars[i]);
            i += 1;
        }
    }

    // Clean up extra parentheses and formatting
    new_result = new_result.replace("( ", "(").replace(" )", ")");

    // Add parameter type annotations as a comment
    if !params.is_empty() {
        let param_list: Vec<String> = params
            .iter()
            .map(|p| format!("{}: {:?}", p.name, p.param_type))
            .collect();
        format!("-- Parameters: {}\n{}", param_list.join(", "), new_result)
    } else {
        new_result
    }
}

/// Try to simplify an abort predicate to a constant True or False.
/// Returns Some(IRNode::Const(Bool)) if it can be proven to always/never abort.
pub fn simplify_abort_predicate(program: &Program, func_id: FunctionID) -> Option<IRNode> {
    let func = program.functions.get(&func_id);
    if func_id.variant != FunctionVariant::Aborts {
        return None;
    }

    let ctx = new_context();
    let result = analyze_abort_body(&ctx, program, func);

    match result {
        AbortAnalysisResult::NeverAborts => Some(IRNode::Const(Const::Bool(false))),
        AbortAnalysisResult::AlwaysAborts => Some(IRNode::Const(Const::Bool(true))),
        _ => None,
    }
}

/// Apply simplified abort conditions to a program.
/// Returns a new program with .aborts function bodies replaced by their simplified versions.
pub fn apply_simplified_aborts(mut program: Program, results: &[(FunctionID, AbortAnalysisResult)]) -> Program {
    for (func_id, result) in results {
        let simplified_body = match result {
            AbortAnalysisResult::NeverAborts => IRNode::Const(Const::Bool(false)),
            AbortAnalysisResult::AlwaysAborts => IRNode::Const(Const::Bool(true)),
            AbortAnalysisResult::MayAbort { simplified_ir, .. } => simplified_ir.clone(),
            AbortAnalysisResult::Unknown => continue, // Keep original
        };

        // Update the function body
        let func = program.functions.get_mut(*func_id);
        func.body = simplified_body;
    }

    program
}

