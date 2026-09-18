// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::anyhow;
use codespan_reporting::{diagnostic::Severity, term::termcolor::Buffer};
use move_command_line_common::insta_assert;
use move_compiler::{diagnostics::filter::unused_for_test_filter_scope, shared::PackagePaths};
use move_model::{model::GlobalEnv, run_model_builder_with_options};
use move_stackless_bytecode::{
    borrow_analysis::BorrowAnalysisProcessor,
    clean_and_optimize::CleanAndOptimizeProcessor,
    control_flow_reconstruction::reconstruct_control_flow,
    eliminate_imm_refs::EliminateImmRefsProcessor,
    escape_analysis::EscapeAnalysisProcessor,
    function_target_pipeline::{
        FunctionHolderTarget, FunctionTargetPipeline, FunctionTargetsHolder, ProcessorResultDisplay,
    },
    livevar_analysis::LiveVarAnalysisProcessor,
    memory_instrumentation::MemoryInstrumentationProcessor,
    mut_ref_instrumentation::MutRefInstrumenter,
    options::ProverOptions,
    package_targets::PackageTargets,
    reaching_def_analysis::ReachingDefProcessor,
};
use regex::Regex;
use std::{
    fs::File,
    io::Read,
    path::{Path, PathBuf},
};

// Extracts lines out of some text file where each line starts with `start` which can be a regular
// expressions. Returns the list of such lines with `start` stripped. Use as in
// `extract_test_directives(file, "// dep:")`.
fn extract_test_directives(path: &Path, start: &str) -> anyhow::Result<Vec<String>> {
    let rex = Regex::new(&format!("(?m)^{}(?P<ann>.*?)$", start)).unwrap();
    let mut content = String::new();
    let mut file = File::open(path)?;
    file.read_to_string(&mut content)?;
    let mut at = 0;
    let mut res = vec![];
    while let Some(cap) = rex.captures(&content[at..]) {
        res.push(cap.name("ann").unwrap().as_str().trim().to_string());
        at += cap.get(0).unwrap().end();
    }
    Ok(res)
}

fn get_tested_transformation_pipeline(
    dir_name: &str,
) -> anyhow::Result<Option<FunctionTargetPipeline>> {
    match dir_name {
        "from_move" => Ok(None),
        "eliminate_imm_refs" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            Ok(Some(pipeline))
        }
        "mut_ref_instrumentation" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            Ok(Some(pipeline))
        }
        "reaching_def" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            Ok(Some(pipeline))
        }
        "conditional_merge_insertion" => {
            use move_stackless_bytecode::conditional_merge_insertion::ConditionalMergeInsertionProcessor;
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(ConditionalMergeInsertionProcessor::new_with_debug());
            Ok(Some(pipeline))
        }
        "livevar" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            Ok(Some(pipeline))
        }
        "borrow" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(BorrowAnalysisProcessor::new());
            Ok(Some(pipeline))
        }
        "borrow_strong" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(BorrowAnalysisProcessor::new());
            Ok(Some(pipeline))
        }
        "escape_analysis" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(Box::new(EscapeAnalysisProcessor {}));
            Ok(Some(pipeline))
        }
        "memory_instr" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(BorrowAnalysisProcessor::new());
            pipeline.add_processor(MemoryInstrumentationProcessor::new());
            Ok(Some(pipeline))
        }
        "clean_and_optimize" => {
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(BorrowAnalysisProcessor::new());
            pipeline.add_processor(MemoryInstrumentationProcessor::new());
            pipeline.add_processor(CleanAndOptimizeProcessor::new());
            Ok(Some(pipeline))
        }
        "control_flow_reconstruction" => {
            // Run the same pipeline as the Lean backend to match its behavior
            let mut pipeline = FunctionTargetPipeline::default();
            pipeline.add_processor(EliminateImmRefsProcessor::new());
            pipeline.add_processor(MutRefInstrumenter::new());
            pipeline.add_processor(ReachingDefProcessor::new());
            pipeline.add_processor(LiveVarAnalysisProcessor::new());
            pipeline.add_processor(BorrowAnalysisProcessor::new());
            pipeline.add_processor(MemoryInstrumentationProcessor::new());
            pipeline.add_processor(CleanAndOptimizeProcessor::new());
            Ok(Some(pipeline))
        }
        _ => Err(anyhow!(
            "the sub-directory `{}` has no associated pipeline to test",
            dir_name
        )),
    }
}

// Prefix of `// dep:` directives that refer to the Move standard library. These paths date
// from when this crate lived next to `move-stdlib` in the Move repository; they are resolved
// against the sources of the `move-stdlib` crate this crate depends on.
const MOVE_STDLIB_DEP_PREFIX: &str = "../move-stdlib/";

// Resolves a `// dep:` directive to a path on disk. Paths are relative to the crate
// directory, except for Move stdlib deps (see `MOVE_STDLIB_DEP_PREFIX`).
fn resolve_dep(dep: &str) -> anyhow::Result<String> {
    let resolved = match dep.strip_prefix(MOVE_STDLIB_DEP_PREFIX) {
        Some(relative) => move_stdlib::path_in_crate(relative),
        None => PathBuf::from(dep),
    };
    if !resolved.exists() {
        return Err(anyhow!(
            "dependency `{}` not found (resolved to `{}`)",
            dep,
            resolved.display()
        ));
    }
    Ok(resolved.to_string_lossy().to_string())
}

fn test_runner(path: &Path) -> datatest_stable::Result<()> {
    // Allow opting out of external deps (e.g., move-stdlib) so isolated tests can run
    // without them. Set env var `STACKLESS_TEST_IGNORE_DEPS=1`.
    let ignore_deps = std::env::var("STACKLESS_TEST_IGNORE_DEPS").is_ok();
    let sources = if ignore_deps {
        vec![path.to_string_lossy().to_string()]
    } else {
        let mut deps = extract_test_directives(path, "// dep:")?
            .iter()
            .map(|dep| resolve_dep(dep))
            .collect::<anyhow::Result<Vec<_>>>()?;
        deps.push(path.to_string_lossy().to_string());
        deps
    };
    let env: GlobalEnv = run_model_builder_with_options(
        vec![PackagePaths {
            name: None,
            paths: sources,
            named_address_map: move_stdlib::named_addresses(),
        }],
        vec![],
        Some(unused_for_test_filter_scope()),
    )?;
    let out = if env.has_errors() {
        let mut error_writer = Buffer::no_color();
        env.report_diag(&mut error_writer, Severity::Error);
        String::from_utf8_lossy(&error_writer.into_inner()).to_string()
    } else {
        let options = ProverOptions {
            stable_test_output: true,
            ..Default::default()
        };
        let dir_name = path
            .parent()
            .and_then(|p| p.file_name())
            .and_then(|p| p.to_str())
            .ok_or_else(|| anyhow!("bad file name"))?;
        let pipeline_opt = get_tested_transformation_pipeline(dir_name)?;

        // Initialize and print function targets
        let mut text = String::new();
        let package_targets = PackageTargets::new(&env, Default::default(), true, None);
        let mut targets =
            FunctionTargetsHolder::new(options, &package_targets, FunctionHolderTarget::All);
        for module_env in env.get_modules() {
            for func_env in module_env.get_functions() {
                targets.add_target(&func_env);
            }
        }
        targets.resolve_loop_invariants(&env);
        let show_livevars = std::env::var("STACKLESS_TEST_SHOW_LIVENESS").is_ok();
        let show_borrow = true;
        let show_reach = std::env::var("STACKLESS_TEST_SHOW_REACHING_DEFS").is_ok();
        text += &move_stackless_bytecode::print_targets_for_test_with_flags(
            &env,
            "initial translation from Move",
            &targets,
            show_livevars,
            show_borrow,
            show_reach,
        );

        // Run pipeline if any
        if let Some(pipeline) = pipeline_opt {
            let _ = pipeline.run(&env, &mut targets);
            let processor = pipeline.last_processor();
            if !processor.is_single_run() {
                text += &move_stackless_bytecode::print_targets_for_test_with_flags(
                    &env,
                    &format!("after pipeline `{}`", dir_name),
                    &targets,
                    show_livevars,
                    show_borrow,
                    show_reach,
                );
            }
            text += &ProcessorResultDisplay {
                env: &env,
                targets: &targets,
                processor,
            }
            .to_string();

            // For control_flow_reconstruction tests, add reconstruction output after pipeline
            if dir_name == "control_flow_reconstruction" {
                text += "\n============ Control Flow Reconstruction ================\n";
                for module_env in env.get_modules() {
                    for func_env in module_env.get_functions() {
                        for (variant, target) in targets.get_targets(&func_env) {
                            if !target.data.code.is_empty() {
                                text += &format!(
                                    "\n[variant {}]\nfun {}::{}\n",
                                    variant,
                                    func_env.module_env.get_name().display(env.symbol_pool()),
                                    func_env.get_name().display(func_env.symbol_pool())
                                );
                                let blocks = reconstruct_control_flow(&target.data.code);
                                text += &format!("{:#?}\n", blocks);
                            }
                        }
                    }
                }
            }
        }
        // add Warning and Error diagnostics to output
        let mut error_writer = Buffer::no_color();
        if env.has_errors() || env.has_warnings() {
            env.report_diag(&mut error_writer, Severity::Warning);
            text += "============ Diagnostics ================\n";
            text += &String::from_utf8_lossy(&error_writer.into_inner());
        }
        text
    };
    // diagnostics in stdlib deps mention their absolute, machine-specific location; replace it
    // with the `../move-stdlib/` prefix the deps are declared with.
    let stdlib_dir = move_stdlib::path_in_crate("").to_string_lossy().to_string();
    let out = out.replace(&stdlib_dir, MOVE_STDLIB_DEP_PREFIX);
    insta_assert! {
        input_path: path,
        contents: out,
    };
    Ok(())
}

datatest_stable::harness! {
    { test = test_runner, root = "tests", pattern = r".*\.move" },
}
