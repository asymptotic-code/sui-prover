// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

//! Lean backend entry point
//!
//! Takes TheoremProgram and renders to Lean files.
//! ZERO logic, pure rendering.

use crate::prelude::PreludeManager;
use crate::renderer::render_to_directory;
use crate::runtime::run_lake_build;
use intermediate_theorem_format::analysis::eliminate_impossible_aborts;
use intermediate_theorem_format::smt::{simplify_aborts, apply_simplified_aborts, AbortAnalysisResult};
use intermediate_theorem_format::{BinOp, Const, FunctionID, FunctionVariant, IRNode, Program, UnOp};
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use move_stackless_bytecode::package_targets::PackageTargets;
use stackless_to_intermediate::ProgramBuilder;
use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::Path;

/// Lean backend - translate IR to Lean
pub async fn run_backend(
    env: &GlobalEnv,
    targets: &FunctionTargetsHolder,
    package_targets: &PackageTargets,
    output_dir: &Path,
    generate_only: bool,
) -> anyhow::Result<()> {
    // Run translation pipeline (spec_targets are set inside build() before finalize()
    // so dependency ordering accounts for spec function body dependencies)
    let program = ProgramBuilder::new(env).build(targets, package_targets);

    // Run SMT simplification on abort predicates
    println!("\n=== SMT Abort Analysis ===");
    let abort_results = simplify_aborts(&program);
    for (func_id, result) in &abort_results {
        let func = program.functions.get(func_id);
        let status = match result {
            AbortAnalysisResult::NeverAborts => "✓ Never aborts".to_string(),
            AbortAnalysisResult::AlwaysAborts => "✗ Always aborts".to_string(),
            AbortAnalysisResult::MayAbort { .. } => "? May abort (conditional)".to_string(),
            AbortAnalysisResult::Unknown => "? Unknown (unsupported constructs)".to_string(),
        };
        println!("  {}: {}", func.name, status);
    }
    println!("=========================\n");

    // Apply simplified abort conditions to the program
    let mut program = apply_simplified_aborts(program, &abort_results);

    // Run Z3-based elimination of impossible abort conditions
    println!("\n=== Z3 Abort Elimination ===");
    eliminate_impossible_aborts(&mut program);
    println!("Eliminated provably-impossible abort conditions");
    println!("============================\n");

    // Clear regenerated directories but preserve Proofs/ (user-written proofs)
    for dir in ["Impls", "Aborts", "Specs", "SpecDefs", "Prelude"] {
        let path = output_dir.join(dir);
        if path.exists() {
            fs::remove_dir_all(&path)?;
        }
    }
    // Also remove generated files in root (lakefile, etc)
    for file in ["lakefile.lean", "lean-toolchain", "lake-manifest.json"] {
        let path = output_dir.join(file);
        if path.exists() {
            fs::remove_file(&path)?;
        }
    }

    // Create directory structure
    fs::create_dir_all(output_dir)?;
    fs::create_dir_all(output_dir.join("Impls"))?;
    fs::create_dir_all(output_dir.join("Aborts"))?;
    fs::create_dir_all(output_dir.join("Specs"))?;
    fs::create_dir_all(output_dir.join("Proofs"))?;

    // Copy Prelude files
    let prelude_manager = PreludeManager::new(output_dir.to_path_buf());
    prelude_manager.initialize()?;

    // Get Prelude imports from actual files being copied
    let prelude_imports = prelude_manager.get_prelude_imports()?;

    // Render to Lean in Impls/ directory with module organization
    // Pass the project directory (parent of output) for proof library lookup
    let project_dir = output_dir.parent().unwrap_or(output_dir);
    let impls_dir = output_dir.join("Impls");
    render_to_directory(&program, &impls_dir, &prelude_imports, project_dir)?;

    // Copy proof library if it exists
    copy_proof_library(project_dir, output_dir)?;

    // Write abort analysis results to Aborts/ directory
    write_abort_conditions(&abort_results, &program, output_dir)?;

    // Generate lakefile and manifest
    crate::write_lakefile(output_dir, "sui_prover_output")?;

    // Skip lake build if generate_only is true
    if generate_only {
        println!("✓ Lean code generated (skipping lake build)");
        return Ok(());
    }

    // Run lake build
    let output_str = output_dir
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("Invalid output path"))?;

    match run_lake_build(output_str).await {
        Ok(output) => {
            println!("\n=== Lake Build Output ===");
            println!("{}", output);
            println!("=== Lake Build Succeeded ===\n");
            println!("Generated Lean files in: {}", output_dir.display());
            Ok(())
        }
        Err(e) => Err(e),
    }
}

/// Write abort condition analysis results to Lean files
fn write_abort_conditions(
    abort_results: &[(FunctionID, AbortAnalysisResult)],
    program: &Program,
    output_dir: &Path,
) -> anyhow::Result<()> {
    let aborts_dir = output_dir.join("Aborts");

    // Collect functions by module (include func_id for later lookup)
    let mut module_conditions: std::collections::HashMap<String, Vec<(FunctionID, String, String, &AbortAnalysisResult)>> =
        std::collections::HashMap::new();

    for (func_id, result) in abort_results {
        let func = program.functions.get(func_id);
        let module = program.modules.get(&func.module_id);
        let module_name = module.name.clone();

        // Get the base function name (without .aborts suffix)
        let base_func_id = func_id.to_variant(FunctionVariant::Pure);
        let base_func = program.functions.get(&base_func_id);

        module_conditions
            .entry(module_name)
            .or_default()
            .push((*func_id, func.name.clone(), base_func.name.clone(), result));
    }

    // Write a file per module
    for (module_name, conditions) in &module_conditions {
        let file_path = aborts_dir.join(format!("{}.lean", module_name));
        let mut file = fs::File::create(&file_path)?;

        writeln!(file, "-- Abort conditions for module: {}", module_name)?;
        writeln!(file, "-- Generated by SMT analysis")?;
        writeln!(file)?;

        for (func_id, func_name, base_name, result) in conditions {
            writeln!(file, "/-")?;
            writeln!(file, "  Function: {}", base_name)?;

            match result {
                AbortAnalysisResult::NeverAborts => {
                    writeln!(file, "  Status: PROVEN - Never aborts")?;
                    writeln!(file, "  The function {} is guaranteed to never abort for any input.", base_name)?;
                }
                AbortAnalysisResult::AlwaysAborts => {
                    writeln!(file, "  Status: PROVEN - Always aborts")?;
                    writeln!(file, "  The function {} will always abort regardless of input.", base_name)?;
                }
                AbortAnalysisResult::MayAbort { .. } => {
                    // Get the actual simplified body from the program (not the stale condition_str)
                    let actual_func = program.functions.get(func_id);
                    let body_str = format_abort_condition(&actual_func.body, program);
                    writeln!(file, "  Status: Conditional abort")?;
                    writeln!(file, "-/")?;
                    writeln!(file)?;
                    writeln!(file, "-- {} aborts when:", func_name)?;
                    writeln!(file, "-- {}", body_str)?;
                    writeln!(file)?;
                    continue; // Skip the closing -/ since we already closed it
                }
                AbortAnalysisResult::Unknown => {
                    writeln!(file, "  Status: Unknown")?;
                    writeln!(file, "  Could not analyze - contains unsupported constructs.")?;
                }
            }
            writeln!(file, "-/")?;
            writeln!(file)?;
        }
    }

    // Write a summary file
    let summary_path = aborts_dir.join("Summary.lean");
    let mut summary = fs::File::create(&summary_path)?;

    writeln!(summary, "-- Abort Analysis Summary")?;
    writeln!(summary, "-- Generated by SMT analysis")?;
    writeln!(summary)?;

    let never_aborts: Vec<_> = abort_results
        .iter()
        .filter(|(_, r)| matches!(r, AbortAnalysisResult::NeverAborts))
        .collect();
    let may_abort: Vec<_> = abort_results
        .iter()
        .filter(|(_, r)| matches!(r, AbortAnalysisResult::MayAbort { .. }))
        .collect();
    let always_aborts: Vec<_> = abort_results
        .iter()
        .filter(|(_, r)| matches!(r, AbortAnalysisResult::AlwaysAborts))
        .collect();
    let unknown: Vec<_> = abort_results
        .iter()
        .filter(|(_, r)| matches!(r, AbortAnalysisResult::Unknown))
        .collect();

    writeln!(summary, "/-")?;
    writeln!(summary, "  === Abort Analysis Summary ===")?;
    writeln!(summary)?;
    writeln!(summary, "  Proven never abort: {} functions", never_aborts.len())?;
    for (func_id, _) in &never_aborts {
        let func = program.functions.get(func_id);
        writeln!(summary, "    - {}", func.name.trim_end_matches(".aborts"))?;
    }
    writeln!(summary)?;
    writeln!(summary, "  May abort (conditional): {} functions", may_abort.len())?;
    for (func_id, _) in &may_abort {
        let func = program.functions.get(func_id);
        writeln!(summary, "    - {}", func.name.trim_end_matches(".aborts"))?;
    }
    if !always_aborts.is_empty() {
        writeln!(summary)?;
        writeln!(summary, "  Always abort: {} functions", always_aborts.len())?;
        for (func_id, _) in &always_aborts {
            let func = program.functions.get(func_id);
            writeln!(summary, "    - {}", func.name.trim_end_matches(".aborts"))?;
        }
    }
    if !unknown.is_empty() {
        writeln!(summary)?;
        writeln!(summary, "  Unknown: {} functions", unknown.len())?;
        for (func_id, _) in &unknown {
            let func = program.functions.get(func_id);
            writeln!(summary, "    - {}", func.name.trim_end_matches(".aborts"))?;
        }
    }
    writeln!(summary, "-/")?;

    Ok(())
}

/// Format an IRNode as a human-readable abort condition
fn format_abort_condition(ir: &IRNode, program: &Program) -> String {
    format_ir(ir, program, 0)
}

fn format_ir(ir: &IRNode, program: &Program, indent: usize) -> String {
    match ir {
        IRNode::Var(name) => name.clone(),
        IRNode::Const(c) => format_const(c),
        IRNode::BinOp { op, lhs, rhs } => {
            let op_str = format_binop(op);
            let lhs_str = format_ir(lhs, program, indent);
            let rhs_str = format_ir(rhs, program, indent);
            format!("({} {} {})", lhs_str, op_str, rhs_str)
        }
        IRNode::UnOp { op, operand } => {
            let operand_str = format_ir(operand, program, indent);
            match op {
                UnOp::Not => format!("¬{}", operand_str),
                UnOp::BitNot => format!("~{}", operand_str),
                UnOp::Cast(bits) => format!("(BoundedNat.convert : _ → BoundedNat (2^{})) {}", bits, operand_str),
            }
        }
        IRNode::Call { function, args, .. } => {
            let func_name = get_function_name(*function, program);
            let args_str: Vec<_> = args.iter().map(|a| format_ir(a, program, indent)).collect();
            if args_str.is_empty() {
                func_name
            } else {
                format!("{}({})", func_name, args_str.join(", "))
            }
        }
        IRNode::If { cond, then_branch, else_branch } => {
            let cond_str = format_ir(cond, program, indent);
            let then_str = format_ir(then_branch, program, indent + 2);
            let else_str = format_ir(else_branch, program, indent + 2);
            format!("if {} then {} else {}", cond_str, then_str, else_str)
        }
        IRNode::Block { children } => {
            if children.is_empty() {
                return "()".to_string();
            }
            if children.len() == 1 {
                return format_ir(&children[0], program, indent);
            }
            // Format as let bindings followed by result
            let mut parts = Vec::new();
            for child in children {
                parts.push(format_ir(child, program, indent));
            }
            // Join with semicolons for multi-statement blocks
            if parts.len() <= 2 {
                parts.join("; ")
            } else {
                format!("{{ {} }}", parts.join("; "))
            }
        }
        IRNode::Let { pattern, value } => {
            let value_str = format_ir(value, program, indent);
            if pattern.len() == 1 {
                format!("let {} := {}", pattern[0], value_str)
            } else {
                format!("let ({}) := {}", pattern.join(", "), value_str)
            }
        }
        IRNode::Return(values) => {
            let vals: Vec<_> = values.iter().map(|v| format_ir(v, program, indent)).collect();
            format!("return {}", vals.join(", "))
        }
        IRNode::Tuple(elems) => {
            let parts: Vec<_> = elems.iter().map(|e| format_ir(e, program, indent)).collect();
            format!("({})", parts.join(", "))
        }
        // For complex nodes we haven't handled, fall back to simple representation
        _ => format!("<complex: {:?}>", std::mem::discriminant(ir)),
    }
}

fn format_const(c: &Const) -> String {
    match c {
        Const::Bool(b) => if *b { "True" } else { "False" }.to_string(),
        Const::UInt { value, bits } => {
            if *bits <= 64 {
                format!("{}", value)
            } else {
                format!("{}_{}", value, bits)
            }
        }
        Const::Address(addr) => format!("@{}", addr),
        Const::Vector { elems, .. } => {
            let parts: Vec<_> = elems.iter().map(format_const).collect();
            format!("[{}]", parts.join(", "))
        }
    }
}

fn format_binop(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::BitAnd => "&&&",
        BinOp::BitOr => "|||",
        BinOp::BitXor => "^^^",
        BinOp::Shl => "<<<",
        BinOp::Shr => ">>>",
        BinOp::And => "∧",
        BinOp::Or => "∨",
        BinOp::Eq => "==",
        BinOp::Neq => "≠",
        BinOp::Lt => "<",
        BinOp::Le => "≤",
        BinOp::Gt => ">",
        BinOp::Ge => "≥",
    }
}

fn get_function_name(func_id: FunctionID, program: &Program) -> String {
    // Try to get the function name from the program
    if let Some(func) = program.functions.iter().find(|(id, _)| *id == func_id).map(|(_, f)| f) {
        let base_name = func.name.trim_end_matches(".aborts").trim_end_matches(".pure");
        match func_id.variant {
            FunctionVariant::Runtime => base_name.to_string(),
            FunctionVariant::Pure => format!("{}.pure", base_name),
            FunctionVariant::Aborts => format!("{}.aborts", base_name),
            _ => base_name.to_string(),
        }
    } else {
        // Fallback: just show the ID
        format!("func_{}", func_id.base)
    }
}

/// Copy proof library from project directory to output directory
fn copy_proof_library(project_dir: &Path, output_dir: &Path) -> anyhow::Result<()> {
    let proofs_src = project_dir.join("Proofs");
    let proofs_dst = output_dir.join("Proofs");

    if !proofs_src.exists() {
        return Ok(());
    }

    // Use recursive copy
    copy_dir_recursive(&proofs_src, &proofs_dst)?;
    Ok(())
}

/// Recursively copy a directory
fn copy_dir_recursive(src: &Path, dst: &Path) -> anyhow::Result<()> {
    if !dst.exists() {
        fs::create_dir_all(dst)?;
    }

    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let path = entry.path();
        let file_name = entry.file_name();
        let dst_path = dst.join(&file_name);

        if path.is_dir() {
            copy_dir_recursive(&path, &dst_path)?;
        } else {
            fs::copy(&path, &dst_path)?;
        }
    }

    Ok(())
}

/// Build mapping from spec function base IDs to their target function base IDs.
/// Uses the #[spec(target = X)] attribute from PackageTargets.
fn build_spec_target_mapping(program: &Program, package_targets: &PackageTargets) -> HashMap<usize, usize> {
    let mut result = HashMap::new();

    // Iterate through all spec->target mappings from PackageTargets
    // all_specs maps target_id -> set of spec_ids
    // We need the reverse: spec_id -> target_id
    for (target_move_id, spec_move_ids) in package_targets.iter_all_specs() {
        // Look up the target function's IR base ID
        let target_ir_id = match program.functions.get_id_for_move_key(target_move_id) {
            Some(id) => id,
            None => continue, // Target function not in IR
        };

        // For each spec function targeting this function
        for spec_move_id in spec_move_ids {
            // Look up the spec function's IR base ID
            if let Some(spec_ir_id) = program.functions.get_id_for_move_key(spec_move_id) {
                result.insert(spec_ir_id, target_ir_id);
            }
        }
    }

    result
}

