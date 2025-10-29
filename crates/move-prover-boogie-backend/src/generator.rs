#![forbid(unsafe_code)]

use std::cell::RefCell;

use crate::generator_options::Options;
use anyhow::anyhow;
use bimap::btree::BiBTreeMap;
use codespan_reporting::{
    diagnostic::Severity,
    term::termcolor::{Buffer, ColorChoice, StandardStream, WriteColor},
};
#[allow(unused_imports)]
use log::{debug, info, warn};
use move_model::{
    code_writer::CodeWriter, model::{FunId, ModuleId, GlobalEnv, QualifiedId}, ty::Type,
};
use crate::boogie_backend::{
    lib::add_prelude,
    boogie_wrapper::BoogieWrapper,
    bytecode_translator::BoogieTranslator,
    options::BoogieFileMode,
};
use move_stackless_bytecode::{
    escape_analysis::EscapeAnalysisProcessor, function_target_pipeline::{
        FunctionHolderTarget, FunctionTargetPipeline, FunctionTargetsHolder, FunctionVariant, VerificationFlavor
    }, number_operation::GlobalNumberOperationState, options::ProverOptions, pipeline_factory
};
use std::{
    fs,
    path::Path,
    time::Instant,
};
use futures::stream::{self, StreamExt};

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

    // Until this point, prover and docgen have same code. Here we part ways.
    if options.run_docgen {
        //return run_docgen(env, &options, error_writer, now);
    }
    // Same for escape analysis
    if options.run_escape {
        return {
            run_escape(env, &options, now);
            Ok(("Escape analysis completed").to_string())
        };
    }

    // Check correct backend versions.
    options.backend.check_tool_versions()?;

    // Check Filter Correctness
    if let Some(err) = options.filter.check_filter_correctness(env) {
        return Err(anyhow!(err));
    }

    // Create and process bytecode
    let now = Instant::now();
    let (targets, _err_processor) = create_and_process_bytecode(&options, env, FunctionHolderTarget::None);
    let trafo_duration = now.elapsed();
    check_errors(
        env,
        &options,
        error_writer,
        // TODO: add _err_processor to this message
        "exiting with bytecode transformation errors",
    )?;

    let output_path = std::path::Path::new(&options.output_path);
    let output_existed = output_path.exists();

    if !output_existed {
        fs::create_dir_all(output_path)?;
    }

    let now = Instant::now();

    if targets.abort_checks_count() == 0 {
        if targets.specs_count(env) == 0 {
            return Ok("🦀 No specifications found in the project. Nothing to verify.".to_owned());
        }

        if targets.verify_specs_count() == 0 {
            return Ok("🦀 No specifications are marked for verification. Nothing to verify.".to_owned());
        }
    }

    if targets.has_spec_boogie_options() && options.backend.boogie_file_mode != BoogieFileMode::Function {
        // TODO: Emit normal warning
        warn!("Boogie options specified in specs can only be used in 'function' boogie file mode.");
    }

    let has_errors = match options.backend.boogie_file_mode {
        BoogieFileMode::Function | BoogieFileMode::Module => run_prover_gradual_mode(env, &options, &targets, error_writer, options.backend.boogie_file_mode.clone()).await?,
        BoogieFileMode::All => run_prover_all_mode(env, &options, &targets, error_writer).await?,
    };

    let total_duration = now.elapsed();
    info!(
        "{:.3}s building, {:.3}s translation, {:.3}s verification",
        build_duration.as_secs_f64(),
        trafo_duration.as_secs_f64(),
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
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<bool> {
    let file_name = "spec_no_abort_check";
    if opt.prover.skip_spec_no_abort {
        println!("⏭️  {file_name}");
        return Ok(false);
    }

    println!("🔄 {file_name}");

    let mut options = opt.clone();
    options.backend.spec_no_abort_check_only = true;
    
    let (code_writer, types) = generate_boogie(env, &options, &targets)?;
    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;
    verify_boogie(env, &options, &targets, code_writer, types, file_name.to_owned(), None).await?;
    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if is_error {
        println!("❌ {file_name}");
        return Ok(true);
    }

    print!("\x1B[1A\x1B[2K");
    println!("✅ {file_name}");

    return Ok(false);
}

async fn run_prover_abort_check<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    opt: &Options,
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<bool> {
    if targets.abort_checks_count() == 0 {
        return Ok(false);
    }
    let mut options = opt.clone();
    options.backend.func_abort_check_only = true;

    let file_name = "funs_abort_check";
    println!("🔄 {file_name}");
    
    let (code_writer, types) = generate_boogie(env, &options, &targets)?;
    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;
    verify_boogie(env, &options, &targets, code_writer, types, file_name.to_owned(), None).await?;
    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if is_error {
        println!("❌ {file_name}");
        return Ok(true);
    }

    print!("\x1B[1A\x1B[2K");
    println!("✅ {file_name}");

    return Ok(false);
}

fn generate_function_bpl<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    qid: &QualifiedId<FunId>,
) -> anyhow::Result<(String, CodeWriter, BiBTreeMap<Type, String>, Option<String>)> {
    env.cleanup();

    let file_name = env.get_function(*qid).get_full_name_str();
    let target_type = FunctionHolderTarget::Function(*qid);
    let (mut targets, _) = create_and_process_bytecode(options, env, target_type);

    let (code_writer, types) = generate_boogie(env, &options, &mut targets)?;

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;

    Ok((file_name, code_writer, types, targets.get_spec_boogie_options(qid).cloned()))
}

fn generate_module_bpl<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    mid: &ModuleId,
) -> anyhow::Result<(String, CodeWriter, BiBTreeMap<Type, String>, Option<String>)> {
    env.cleanup();

    let file_name = env.get_module(*mid).get_full_name_str();
    let target_type = FunctionHolderTarget::Module(*mid);

    let (mut targets, _) = create_and_process_bytecode(options, env, target_type);

    let (code_writer, types) = generate_boogie(env, &options, &mut targets)?;

    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;
    // Note: Module-level boogie options are not supported yet
    Ok((file_name, code_writer, types, None))
}

async fn verify_bpl<W: WriteColor>(env: &GlobalEnv, error_writer: &mut W,  options: &Options, targets: &FunctionTargetsHolder, file: (String, CodeWriter, BiBTreeMap<Type, String>, Option<String>)) -> anyhow::Result<bool> {
    let (file_name, code_writer, types, boogie_options) = file;
    println!("🔄 {file_name}");

    verify_boogie(env, &options, targets, code_writer, types, file_name.clone(), boogie_options).await?;

    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if is_error {
        println!("❌ {file_name}");
    } else {
        if options.remote.is_none() {
            print!("\x1B[1A\x1B[2K");
        }
        println!("✅ {file_name}");
    }

    Ok(is_error)
}

pub async fn run_prover_gradual_mode<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    all_targets: &FunctionTargetsHolder,
    error_writer: &mut W,
    mode: BoogieFileMode,
) -> anyhow::Result<bool> {
    let error = run_prover_spec_no_abort_check(env, error_writer, options, &all_targets).await?;
    if error {
        return Ok(true);
    }

    let error = run_prover_abort_check(env, error_writer, options, &all_targets).await?;
    if error {
        return Ok(true);
    }

    let mut has_errors = false;

    let mut files = vec![];
    match mode {
        BoogieFileMode::Function => {
            let fun_targets = all_targets
                .specs()
                .filter(|target| 
                    env.get_function(**target).module_env.is_target() && 
                    all_targets.is_verified_spec(target)
                ).collect::<Vec<_>>();

            for qid in fun_targets {
                let res = generate_function_bpl(env, options, error_writer, qid)?;
                files.push(res);
            }
        },
        BoogieFileMode::Module => {
            let module_targets = all_targets
                .target_modules()
                .into_iter()
                .filter(|target| env.get_module(**target).is_target())
                .collect::<Vec<_>>();

            for mid in module_targets {
                let res = generate_module_bpl(env, options, error_writer, mid)?;
                files.push(res);
            }
        }
        BoogieFileMode::All => unreachable!(),
    }

    if options.remote.is_some() {
        let results = stream::iter(files)
            .map(|file| {
                async move {
                    let mut local_error_writer = Buffer::no_color();
                    let is_error = verify_bpl(env, &mut local_error_writer, options, all_targets, file).await;
                    (local_error_writer, is_error)
                }
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
            let is_error = verify_bpl(env, error_writer, options, all_targets, file).await?;
            if is_error {
                has_errors = true;
            }
        }
    }

    for skip_spec in all_targets.skip_specs() {
        let fun_env = env.get_function(*skip_spec);
        let txt = all_targets.skip_spec_txt(skip_spec);
        let loc = fun_env.get_loc().display_line_only(env).to_string();
        let name = fun_env.get_full_name_str();
        if txt.is_empty() {
            println!("⏭️ {} {}", name, loc);
        } else {
            println!("⏭️ {} {}: {}", name, loc, txt);
        }
    }

    Ok(has_errors)
}

pub async fn run_prover_all_mode<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
    error_writer: &mut W,
) -> anyhow::Result<bool> {    
    let error = run_prover_abort_check(env, error_writer, options, targets).await?;
    if error {
        return Ok(true);
    }

    let (code_writer, types) = generate_boogie(env, &options, &targets)?;
    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors",
    )?;

    verify_boogie(env, &options, &targets, code_writer, types, "output".to_string(), None).await?;

    let errors = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);
    if errors {
        return Ok(true);
    }

    for spec in targets.specs() {
        let fun_env = env.get_function(*spec);
        if targets.is_verified_spec(spec)
            && targets.has_target(
                &fun_env,
                &FunctionVariant::Verification(VerificationFlavor::Regular),
            )
        {
            println!("✅ {}", fun_env.get_full_name_str());
        }
    }    

    Ok(false)
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
) -> anyhow::Result<(CodeWriter, BiBTreeMap<Type, String>)> {
    let writer = CodeWriter::new(env.internal_loc());
    let types = RefCell::new(BiBTreeMap::new());
    add_prelude(env, &options.backend, &writer)?;
    let mut translator = BoogieTranslator::new(env, &options.backend, targets, &writer, &types);
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
            boogie.call_remote_boogie_and_verify_output(&file_name, &options.remote.as_ref().unwrap(), boogie_options).await?;
        } else {
            boogie.call_boogie_and_verify_output(&file_name, boogie_options)?;
        }
    }

    Ok(())
}

/// Create bytecode and process it.
pub fn create_and_process_bytecode(
    options: &Options,
    env: &GlobalEnv,
    target_type: FunctionHolderTarget,
) -> (FunctionTargetsHolder, Option<String>) {
    // Populate initial number operation state for each function and struct based on the pragma
    create_init_num_operation_state(env, &options.prover);

    let mut targets = FunctionTargetsHolder::new(
        options.prover.clone(),
        options.filter.clone(),
        target_type,
    );

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

fn run_escape(env: &GlobalEnv, options: &Options, now: Instant) {
    let mut targets = FunctionTargetsHolder::new(
        options.prover.clone(),
        options.filter.clone(),
        FunctionHolderTarget::None,
    );
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
