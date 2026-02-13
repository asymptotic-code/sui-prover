#![forbid(unsafe_code)]

use std::cell::RefCell;

use crate::boogie_backend::bytecode_translator::AssertsMode;
use crate::boogie_backend::{
    boogie_wrapper::BoogieWrapper, bytecode_translator::BoogieTranslator, lib::add_prelude,
    options::BoogieFileMode,
};
use crate::generator_options::Options;
use anyhow::anyhow;
use bimap::btree::BiBTreeMap;
use codespan_reporting::{
    diagnostic::Severity,
    term::termcolor::{Buffer, ColorChoice, StandardStream, WriteColor},
};
use futures::stream::{self, StreamExt};
#[allow(unused_imports)]
use log::{debug, info, warn, LevelFilter};
use move_model::{
    code_writer::CodeWriter,
    model::{FunId, GlobalEnv, ModuleId, QualifiedId},
    ty::Type,
};
use move_stackless_bytecode::package_targets::PackageTargets;
use move_stackless_bytecode::{
    escape_analysis::EscapeAnalysisProcessor,
    function_target_pipeline::{
        FunctionHolderTarget, FunctionTargetPipeline, FunctionTargetsHolder,
    },
    number_operation::GlobalNumberOperationState,
    options::ProverOptions,
    pipeline_factory, spec_hierarchy,
};
use std::{fs, path::Path, time::Instant};

pub struct FileOptions {
    pub file_name: String,
    pub code_writer: CodeWriter,
    pub types: BiBTreeMap<Type, String>,
    pub boogie_options: Option<String>,
    pub timeout: Option<u64>,
    pub targets: FunctionTargetsHolder,
    pub qid: Option<QualifiedId<FunId>>,
}

pub fn create_init_num_operation_state(env: &GlobalEnv, prover_options: &ProverOptions) {
    let mut global_state = GlobalNumberOperationState::new_with_options(prover_options.clone());
    for module_env in env.get_modules() {
        for struct_env in module_env.get_structs() {
            global_state.create_initial_struct_oper_state(&struct_env);
        }
        for fun_env in module_env.get_functions() {
            global_state.create_initial_func_oper_state(&fun_env);
        }
    }
    //global_state.create_initial_exp_oper_state(env);
    env.set_extension(global_state);
}

pub async fn run_boogie_gen(env: &GlobalEnv, options: Options) -> anyhow::Result<String> {
    let mut error_writer = StandardStream::stderr(ColorChoice::Auto);

    run_move_prover_with_model(env, &mut error_writer, options, None).await
}

pub async fn run_move_prover_with_model<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    options: Options,
    timer: Option<Instant>,
) -> anyhow::Result<String> {
    let now = timer.unwrap_or_else(Instant::now);

    let build_duration = now.elapsed();
    check_errors(
        env,
        &options,
        error_writer,
        "exiting with model building errors",
    )?;
    // TODO: delete duplicate diagnostics reporting
    env.report_diag(error_writer, options.prover.report_severity);

    let targets = PackageTargets::new(
        &env,
        options.filter.clone(),
        !options.prover.ci,
        options.backend.prelude_extra.as_deref(),
    );

    // Until this point, prover and docgen have same code. Here we part ways.
    if options.run_docgen {
        //return run_docgen(env, &options, error_writer, now);
    }
    // Same for escape analysis
    if options.run_escape {
        return {
            run_escape(env, &targets, &options, now);
            Ok(("Escape analysis completed").to_string())
        };
    }

    if options.remote.is_none() {
        // Check correct backend versions.
        options.backend.check_tool_versions()?;
    }

    // Check Filter Correctness
    if let Some(err) = options.filter.check_filter_correctness(env) {
        return Err(anyhow!(err));
    }

    let output_path = std::path::Path::new(&options.output_path);
    let output_existed = output_path.exists();

    if !output_existed {
        fs::create_dir_all(output_path)?;
    }

    if targets.target_no_abort_check_functions().is_empty() {
        if !targets.has_specs() {
            return Ok("🦀 No specifications found in the project. Nothing to verify.".to_owned());
        }

        if targets.target_specs().is_empty() {
            return Ok(
                "🦀 No specifications are marked for verification. Nothing to verify.".to_owned(),
            );
        }
    }

    let now = Instant::now();

    let has_errors = run_prover(env, &options, &targets, error_writer).await?;

    let total_duration = now.elapsed();
    info!(
        "{:.3}s building, {:.3}s verification",
        build_duration.as_secs_f64(),
        total_duration.as_secs_f64()
    );

    if !output_existed && !options.backend.keep_artifacts {
        std::fs::remove_dir_all(&options.output_path).unwrap_or_default();
    }

    if has_errors {
        return Err(anyhow!("exiting with verification errors"));
    }

    Ok(("Verification successful").to_string())
}

async fn run_prover_spec_no_abort_check<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    opt: &Options,
    targets: &PackageTargets,
) -> anyhow::Result<bool> {
    let file_name = "spec_no_abort_check";

    let targets_modules = targets.spec_abort_check_verify_modules();
    if targets_modules.is_empty() || opt.prover.skip_spec_no_abort {
        return Ok(false);
    }

    let mut options = opt.clone();
    options.backend.spec_no_abort_check_only = true;

    let start_time = Instant::now();
    let files = targets_modules
        .iter()
        .map(|mid| {
            generate_module_bpl(
                env,
                &options,
                error_writer,
                targets,
                mid,
                AssertsMode::SpecNoAbortCheck,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    let elapsed = start_time.elapsed();
    let has_errors = verify_batch(&options, env, error_writer, files).await?;
    env.report_diag(error_writer, options.prover.report_severity);

    if has_errors {
        println!("❌ {} ({:.1}s)", file_name, elapsed.as_secs_f64());
    }

    return Ok(has_errors);
}

async fn run_prover_abort_check<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    opt: &Options,
    package_targets: &PackageTargets,
) -> anyhow::Result<bool> {
    if opt.prover.skip_fun_no_abort {
        return Ok(false);
    }

    let mut options = opt.clone();
    options.backend.func_abort_check_only = true;

    let (targets, _) = create_and_process_bytecode(
        &options,
        env,
        package_targets,
        FunctionHolderTarget::FunctionsAbortCheck,
    );

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with bytecode transformation errors",
    )?;

    if !package_targets
        .abort_check_functions()
        .iter()
        .chain(package_targets.pure_functions().iter())
        .any(|qid| targets.should_generate_abort_check(qid))
    {
        return Ok(false);
    }

    let file_name = "funs_abort_check";
    println!("🔄 {file_name}");

    let mut extra_bpl_contents: Vec<&str> = Vec::new();
    let mut seen_modules = std::collections::BTreeSet::new();
    for qid in package_targets
        .abort_check_functions()
        .iter()
        .chain(package_targets.pure_functions().iter())
    {
        if let Some(content) = package_targets.get_function_extra_bpl(qid) {
            extra_bpl_contents.push(content.as_str());
        }
        if seen_modules.insert(qid.module_id) {
            if let Some(content) = package_targets.get_module_extra_bpl(&qid.module_id) {
                extra_bpl_contents.push(content.as_str());
            }
        }
    }

    let (code_writer, types) = generate_boogie(
        env,
        &options,
        &targets,
        AssertsMode::Check,
        &extra_bpl_contents,
    )?;
    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;
    let start_time = Instant::now();
    verify_boogie(
        env,
        &options,
        &targets,
        code_writer,
        types,
        file_name.to_owned(),
        None,
        None,
    )
    .await?;
    let elapsed = start_time.elapsed();
    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if is_error {
        println!("❌ {} ({:.1}s)", file_name, elapsed.as_secs_f64());
        return Ok(true);
    }

    if !options.backend.trace {
        print!("\x1B[1A\x1B[2K");
    }
    if elapsed.as_secs() > 1 {
        println!("✅ {} ({}s)", file_name, elapsed.as_secs());
    } else {
        println!("✅ {file_name}");
    }

    return Ok(false);
}

fn generate_function_bpl<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    package_targets: &PackageTargets,
    qid: &QualifiedId<FunId>,
    asserts_mode: AssertsMode,
) -> anyhow::Result<FileOptions> {
    env.cleanup();

    let file_name = format!(
        "{}_{:?}",
        env.get_function(*qid).get_full_name_str(),
        asserts_mode
    );
    let target_type = FunctionHolderTarget::Function(*qid);
    let (mut targets, _) = create_and_process_bytecode(options, env, package_targets, target_type);

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with bytecode transformation errors",
    )?;

    let mut extra_bpl_contents: Vec<&str> = Vec::new();
    if let Some(content) = package_targets.get_function_extra_bpl(qid) {
        extra_bpl_contents.push(content.as_str());
    }
    if let Some(content) = package_targets.get_module_extra_bpl(&qid.module_id) {
        extra_bpl_contents.push(content.as_str());
    }

    let (code_writer, types) = generate_boogie(
        env,
        &options,
        &mut targets,
        asserts_mode,
        &extra_bpl_contents,
    )?;

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;

    Ok(FileOptions {
        file_name,
        code_writer,
        types,
        boogie_options: targets.get_spec_boogie_options(qid).cloned(),
        timeout: targets.get_spec_timeout(qid).cloned(),
        targets,
        qid: Some(*qid),
    })
}

fn generate_module_bpl<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    package_targets: &PackageTargets,
    mid: &ModuleId,
    asserts_mode: AssertsMode,
) -> anyhow::Result<FileOptions> {
    env.cleanup();

    let file_name = format!(
        "{}_{:?}",
        env.get_module(*mid).get_full_name_str(),
        asserts_mode
    );
    let target_type = if asserts_mode == AssertsMode::SpecNoAbortCheck {
        FunctionHolderTarget::SpecNoAbortCheck(*mid)
    } else {
        FunctionHolderTarget::Module(*mid)
    };

    let (mut targets, _) = create_and_process_bytecode(options, env, package_targets, target_type);

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with bytecode transformation errors",
    )?;

    let extra_bpl_contents: Vec<&str> = package_targets
        .get_module_extra_bpl(mid)
        .into_iter()
        .map(|s| s.as_str())
        .collect();

    let (code_writer, types) = generate_boogie(
        env,
        &options,
        &mut targets,
        asserts_mode,
        &extra_bpl_contents,
    )?;

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;
    // Note: Module-level boogie options / timeouts are not supported yet
    Ok(FileOptions {
        file_name,
        code_writer,
        types,
        boogie_options: None,
        timeout: None,
        targets,
        qid: None,
    })
}

async fn verify_bpl<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    options: &Options,
    file: FileOptions,
) -> anyhow::Result<bool> {
    println!("🔄 {}", file.file_name);

    let start_time = Instant::now();
    verify_boogie(
        env,
        &options,
        &file.targets,
        file.code_writer,
        file.types,
        file.file_name.clone(),
        file.timeout,
        file.boogie_options,
    )
    .await?;
    let elapsed = start_time.elapsed();

    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if is_error {
        println!("❌ {} ({:.1}s)", file.file_name, elapsed.as_secs_f64());
    } else {
        if options.remote.is_none() && !options.backend.trace {
            print!("\x1B[1A\x1B[2K");
        }
        if elapsed.as_secs() > 1 {
            println!("✅ {} ({}s)", file.file_name, elapsed.as_secs());
        } else {
            println!("✅ {}", file.file_name);
        }
    }

    if let Some(qid) = &file.qid {
        if options.verbosity_level > LevelFilter::Info {
            if file.file_name.ends_with("_Check") {
                spec_hierarchy::display_spec_tree_terminal(env, &file.targets, qid);
            }
        }
    }

    Ok(is_error)
}

pub async fn run_prover<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    targets: &PackageTargets,
    error_writer: &mut W,
) -> anyhow::Result<bool> {
    let error = run_prover_spec_no_abort_check(env, error_writer, options, targets).await?;
    if error {
        return Ok(true);
    }

    let error = run_prover_abort_check(env, error_writer, options, targets).await?;
    if error {
        return Ok(true);
    }

    if targets.target_specs().is_empty() {
        return Ok(false);
    }

    if matches!(options.backend.boogie_file_mode, BoogieFileMode::Module)
        && targets.has_spec_boogie_options()
    {
        warn!("Boogie options specified in specs can only be used in 'function' boogie file mode.");
    }

    let files = match options.backend.boogie_file_mode {
        BoogieFileMode::Function => {
            let mut result = Vec::new();
            result.extend(
                targets
                    .target_specs()
                    .iter()
                    .map(|qid| {
                        generate_function_bpl(
                            env,
                            options,
                            error_writer,
                            targets,
                            qid,
                            AssertsMode::Check,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            result.extend(
                targets
                    .target_specs()
                    .iter()
                    .map(|qid| {
                        generate_function_bpl(
                            env,
                            options,
                            error_writer,
                            targets,
                            qid,
                            AssertsMode::Assume,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            result.extend(
                targets
                    .target_specs()
                    .iter()
                    .map(|qid| {
                        generate_function_bpl(
                            env,
                            options,
                            error_writer,
                            targets,
                            qid,
                            AssertsMode::SpecNoAbortCheck,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );

            result
        }
        BoogieFileMode::Module => {
            let mut result = Vec::new();
            result.extend(
                targets
                    .target_modules()
                    .iter()
                    .map(|mid| {
                        generate_module_bpl(
                            env,
                            options,
                            error_writer,
                            targets,
                            mid,
                            AssertsMode::Check,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            result.extend(
                targets
                    .target_modules()
                    .iter()
                    .map(|mid| {
                        generate_module_bpl(
                            env,
                            options,
                            error_writer,
                            targets,
                            mid,
                            AssertsMode::Assume,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            result.extend(
                targets
                    .target_modules()
                    .iter()
                    .map(|mid| {
                        generate_module_bpl(
                            env,
                            options,
                            error_writer,
                            targets,
                            mid,
                            AssertsMode::SpecNoAbortCheck,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );

            result
        }
    };

    let has_errors = verify_batch(options, env, error_writer, files).await?;

    for (qid, reason) in targets.skipped_specs().iter() {
        let fun_env = env.get_function(*qid);
        let loc = fun_env.get_loc().display_line_only(env).to_string();
        let name = fun_env.get_full_name_str();
        if reason.is_empty() {
            println!("⏭️ {} {}", name, loc);
        } else {
            println!("⏭️ {} {}: {}", name, loc, reason);
        }
    }

    Ok(has_errors)
}

async fn verify_batch<W: WriteColor>(
    options: &Options,
    env: &GlobalEnv,
    error_writer: &mut W,
    files: Vec<FileOptions>,
) -> anyhow::Result<bool> {
    let mut has_errors = false;
    if options.remote.is_some() {
        let results = stream::iter(files)
            .map(|file| async move {
                let mut local_error_writer = Buffer::no_color();
                let is_error = verify_bpl(env, &mut local_error_writer, options, file).await;
                (local_error_writer, is_error)
            })
            .buffer_unordered(options.remote.as_ref().unwrap().concurrency)
            .collect::<Vec<_>>()
            .await;

        for (local_error_writer, is_error) in results {
            error_writer.write_all(&local_error_writer.into_inner())?;
            if is_error? {
                has_errors = true;
            }
        }
    } else {
        for file in files {
            let is_error = verify_bpl(env, error_writer, options, file).await?;
            if is_error {
                has_errors = true;
            }
        }
    }

    Ok(has_errors)
}

pub fn check_errors<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    msg: &'static str,
) -> anyhow::Result<()> {
    let errors = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);
    if errors {
        Err(anyhow!(msg))
    } else {
        Ok(())
    }
}

pub fn generate_boogie(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
    asserts_mode: AssertsMode,
    extra_bpl_contents: &[&str],
) -> anyhow::Result<(CodeWriter, BiBTreeMap<Type, String>)> {
    let writer = CodeWriter::new(env.internal_loc());
    let types = RefCell::new(BiBTreeMap::new());
    add_prelude(env, targets, &options.backend, &writer, extra_bpl_contents)?;
    let mut translator = BoogieTranslator::new(
        env,
        &options.backend,
        targets,
        &writer,
        &types,
        asserts_mode,
    );
    translator.translate();
    Ok((writer, types.into_inner()))
}

pub async fn verify_boogie(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
    writer: CodeWriter,
    types: BiBTreeMap<Type, String>,
    target_name: String,
    timeout: Option<u64>,
    boogie_options: Option<String>,
) -> anyhow::Result<()> {
    let file_name = format!("{}/{}.bpl", options.output_path, target_name);

    debug!("writing boogie to `{}`", &file_name);

    writer.process_result(|result| fs::write(&file_name, result))?;

    if !options.prover.generate_only {
        let boogie = BoogieWrapper {
            env,
            targets,
            writer: &writer,
            options: &options.backend,
            types: &types,
        };
        if options.remote.is_some() {
            boogie
                .call_remote_boogie_and_verify_output(
                    &file_name,
                    &options.remote.as_ref().unwrap(),
                    timeout,
                    boogie_options,
                )
                .await?;
        } else {
            boogie.call_boogie_and_verify_output(&file_name, timeout, boogie_options)?;
        }
    }

    Ok(())
}

/// Create bytecode and process it.
pub fn create_and_process_bytecode(
    options: &Options,
    env: &GlobalEnv,
    package_targets: &PackageTargets,
    target_type: FunctionHolderTarget,
) -> (FunctionTargetsHolder, Option<String>) {
    let mut targets =
        FunctionTargetsHolder::new(options.prover.clone(), package_targets, target_type);

    let output_dir = Path::new(&options.output_path)
        .parent()
        .expect("expect the parent directory of the output path to exist");
    let output_prefix = options.move_sources.first().map_or("bytecode", |s| {
        Path::new(s).file_name().unwrap().to_str().unwrap()
    });

    // Add function targets for all functions in the environment.
    for module_env in env.get_modules() {
        if module_env.is_target() {
            info!("preparing module {}", module_env.get_full_name_str());
        }
        if options.prover.dump_bytecode {
            let dump_file = output_dir.join(format!("{}.mv.disas", output_prefix));
            fs::write(&dump_file, module_env.disassemble()).expect("dumping disassembled module");
        }
        for func_env in module_env.get_functions() {
            targets.add_target(&func_env);
        }
    }

    // Populate initial number operation state for each function and struct based on the pragma
    create_init_num_operation_state(env, &options.prover);

    // Create processing pipeline and run it.
    let pipeline = if options.experimental_pipeline {
        pipeline_factory::experimental_pipeline()
    } else {
        pipeline_factory::default_pipeline_with_options(&options.prover)
    };

    let res = if options.prover.dump_bytecode {
        let dump_file_base = output_dir
            .join(output_prefix)
            .into_os_string()
            .into_string()
            .unwrap();
        pipeline.run_with_dump(env, &mut targets, &dump_file_base, options.prover.dump_cfg)
    } else {
        pipeline.run(env, &mut targets)
    };

    (targets, res.err().map(|p| p.name()))
}

// Tools using the Move prover top-level driver
// ============================================
/*
fn run_docgen<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    now: Instant,
) -> anyhow::Result<()> {
    let generator = Docgen::new(env, &options.docgen);
    let checking_elapsed = now.elapsed();
    info!("generating documentation");
    for (file, content) in generator.gen() {
        let path = PathBuf::from(&file);
        fs::create_dir_all(path.parent().unwrap())?;
        fs::write(path.as_path(), content)?;
    }
    let generating_elapsed = now.elapsed();
    info!(
        "{:.3}s checking, {:.3}s generating",
        checking_elapsed.as_secs_f64(),
        (generating_elapsed - checking_elapsed).as_secs_f64()
    );
    if env.has_errors() {
        env.report_diag(error_writer, options.prover.report_severity);
        Err(anyhow!("exiting with documentation generation errors"))
    } else {
        Ok(())
    }
}
*/

fn run_escape(env: &GlobalEnv, targets: &PackageTargets, options: &Options, now: Instant) {
    let mut targets =
        FunctionTargetsHolder::new(options.prover.clone(), targets, FunctionHolderTarget::All);
    for module_env in env.get_modules() {
        for func_env in module_env.get_functions() {
            targets.add_target(&func_env);
        }
    }
    println!(
        "Analyzing {} modules, {} declared functions, {} declared structs, {} total bytecodes",
        env.get_module_count(),
        env.get_declared_function_count(),
        env.get_declared_struct_count(),
        env.get_move_bytecode_instruction_count(),
    );
    let mut pipeline = FunctionTargetPipeline::default();
    pipeline.add_processor(EscapeAnalysisProcessor::new());

    let start = now.elapsed();
    let _ = pipeline.run(env, &mut targets);
    let end = now.elapsed();

    // print escaped internal refs flagged by analysis. do not report errors in dependencies
    let mut error_writer = Buffer::no_color();
    env.report_diag_with_filter(&mut error_writer, |d| {
        let fname = env.get_file(d.labels[0].file_id).to_str().unwrap();
        options.move_sources.iter().any(|d| {
            let p = Path::new(d);
            if p.is_file() {
                d == fname
            } else {
                Path::new(fname).parent().unwrap() == p
            }
        }) && d.severity >= Severity::Error
    });
    println!("{}", String::from_utf8_lossy(&error_writer.into_inner()));
    info!("in ms, analysis took {:.3}", (end - start).as_millis())
}
