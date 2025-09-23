#![forbid(unsafe_code)]

use std::{cell::RefCell, io::Write};

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
        FunctionTargetPipeline, FunctionTargetsHolder, FunctionVariant, VerificationFlavor,
    }, number_operation::GlobalNumberOperationState, options::ProverOptions, pipeline_factory
};
use std::{
    fs,
    path::Path,
    time::Instant,
};

pub fn create_init_num_operation_state(env: &GlobalEnv) {
    let mut global_state: GlobalNumberOperationState = Default::default();
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
        "exiting with model building errors".to_string(),
    )?;
    // TODO: delete duplicate diagnostics reporting
    env.report_diag(error_writer, options.prover.report_severity);

    // Add the prover options as an extension to the environment, so they can be accessed
    // from there.
    ProverOptions::set(env, options.prover.clone());

    // Populate initial number operation state for each function and struct based on the pragma
    create_init_num_operation_state(env);

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
    let trafo_duration = now.elapsed();

    let output_path = std::path::Path::new(&options.output_path);
    let output_existed = output_path.exists();

    if !output_existed {
        fs::create_dir_all(output_path)?;
    }

    // create first time to check for errors and get general metrics
    let mut targets: FunctionTargetsHolder = FunctionTargetsHolder::new(Some(options.filter.clone()));
    let _err_processor = create_and_process_bytecode(&options, env, &mut targets);
    let error_text = format!("exiting with bytecode transformation errors: {}", _err_processor.unwrap_or("unknown".to_string()));
    check_errors(
        env,
        &options,
        error_writer,
        error_text,
    )?;

    if targets.abort_checks_count() == 0 {
        if targets.specs_count(env) == 0 {
            return Ok("🦀 No specifications found in the project. Nothing to verify.".to_owned());
        }

        if targets.verify_specs_count() == 0 {
            return Ok("🦀 No specifications are marked for verification. Nothing to verify.".to_owned());
        }
    }

    let (has_errors, internal_writer) = match options.backend.boogie_file_mode {
        BoogieFileMode::Function => run_prover_function_mode(env, &options, &targets).await?,
        BoogieFileMode::Module => run_prover_module_mode(env, &options, &targets).await?,
        BoogieFileMode::All => run_prover_all_mode(env, &options, &targets).await?,
    };

    error_writer.write(&internal_writer.into_inner())?;

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
    println!("🔄 {file_name}");

    let mut options = opt.clone();
    options.backend.spec_no_abort_check_only = true;
    
    let (code_writer, types) = generate_boogie(env, &options, &targets)?;
    check_errors(
        env,
        &options,
        error_writer,
        "exiting with condition generation errors".to_string(),
    )?;
    verify_boogie(env, &options, &targets, code_writer, types, file_name.to_owned()).await?;
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
        "exiting with condition generation errors".to_string(),
    )?;
    verify_boogie(env, &options, &targets, code_writer, types, file_name.to_owned()).await?;
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

async fn process_fn<W: WriteColor>(global_env: &GlobalEnv, error_writer: &mut W, options: &Options, qid: &QualifiedId<FunId>) -> anyhow::Result<bool> {
    let env = global_env.clone();
    let fun_env = env.get_function(*qid);

    let mut targets = FunctionTargetsHolder::new_with_qid(Some(options.filter.clone()), *qid);
    create_and_process_bytecode(&options, &env, &mut targets); // unwrap should be safe here as we checked for errors before

    let has_target = targets.has_target(
        &fun_env,
        &FunctionVariant::Verification(VerificationFlavor::Regular),
    );

    let file_name = fun_env.get_full_name_str();

    if has_target {
        println!("🔄 {file_name}");
    }

    let (code_writer, types) = generate_boogie(&env, &options, &targets)?;

    check_errors(
        &env,
        &options,
        error_writer,
        "exiting with condition generation errors".to_string(),
    )?;

    verify_boogie(&env, &options, &targets, code_writer, types, file_name.clone()).await?;

    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if has_target {
        if is_error {
            println!("❌ {file_name}");
        } else {
            if options.remote.is_none() {
                print!("\x1B[1A\x1B[2K");
            }
            println!("✅ {file_name}");
        }
    }

    Ok(is_error)
}

pub async fn run_prover_function_mode(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<(bool, Buffer)> {
    let mut error_writer = Buffer::no_color();
    let error = run_prover_spec_no_abort_check(env, &mut error_writer, options, targets).await?;
    if error {
        return Ok((true, error_writer));
    }

    let error = run_prover_abort_check(env, &mut error_writer, options, targets).await?;
    if error {
        return Ok((true, error_writer));
    }

    let mut has_errors = false;

    let fun_targets = targets.specs().filter(|target| 
        env.get_function(**target).module_env.is_target() && 
        targets.is_verified_spec(target)
    ).collect::<Vec<_>>();

    if options.remote.is_some() {
        for batch in fun_targets.chunks(options.remote.as_ref().unwrap().concurrency) {
            let results = futures::future::join_all(
                batch.iter().map(|func| async {
                    let mut local_error_writer = Buffer::no_color();
                    let is_error = process_fn(env, &mut local_error_writer, options, *func).await;
                    (local_error_writer, is_error)
                })
            ).await;

            for (writer, is_error) in results {
                if is_error? {
                    has_errors = true;
                }
                error_writer.write(&writer.into_inner())?;
            }
        }
    } else {
        for target in fun_targets {
            let is_error = process_fn(env, &mut error_writer, options, target).await?;
            if is_error {
                has_errors = true;
            }
        }
    }

    for skip_spec in targets.skip_specs() {
        let fun_env = env.get_function(*skip_spec);
        let txt = targets.skip_spec_txt(skip_spec);
        let loc = fun_env.get_loc().display_line_only(env).to_string();
        let name = fun_env.get_full_name_str();
        if txt.is_empty() {
            println!("⏭️ {} {}", name, loc);
        } else {
            println!("⏭️ {} {}: {}", name, loc, txt);
        }
    }

    Ok((has_errors, error_writer))
}

pub async fn run_prover_all_mode(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<(bool, Buffer)> {
    let mut error_writer = Buffer::no_color();
    
    let error = run_prover_abort_check(env, &mut error_writer, options, targets).await?;
    if error {
        return Ok((true, error_writer));
    }

    let (code_writer, types) = generate_boogie(env, &options, &targets)?;
    check_errors(
        env,
        &options,
        &mut error_writer,
        "exiting with condition generation errors".to_string(),
    )?;

    verify_boogie(env, &options, &targets, code_writer, types, "output".to_string()).await?;

    let errors = env.has_errors();
    env.report_diag(&mut error_writer, options.prover.report_severity);
    if errors {
        return Ok((true, error_writer));
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

    Ok((false, error_writer))
}

async fn process_mod<W: WriteColor>(global_env: &GlobalEnv, error_writer: &mut W, options: &Options, mid: &ModuleId) -> anyhow::Result<bool> {
    let env = global_env.clone();
    let module_env = env.get_module(*mid);
    let file_name = module_env.get_full_name_str();
    let mut targets: FunctionTargetsHolder = FunctionTargetsHolder::new_with_mid(Some(options.filter.clone()), *mid);
    create_and_process_bytecode(&options, &env, &mut targets).unwrap(); // unwrap should be safe here as we checked for errors before

    println!("🔄 {file_name}");

    let (code_writer, types) = generate_boogie(&env, &options, &targets)?;

    check_errors(
        &env,
        &options,
        error_writer,
        "exiting with condition generation errors".to_string(),
    )?;

    verify_boogie(&env, &options, &targets, code_writer, types, file_name.clone()).await?;

    let is_error = env.has_errors();
    env.report_diag(error_writer, options.prover.report_severity);

    if is_error {
        println!("❌ {file_name}");
    } else {
        if options.remote.is_none() {
            print!("\x1B[1A\x1B[2K");
        }
        println!("✅ {file_name}");
        for spec in targets.specs() {
            let fun_env = env.get_function(*spec);
            if targets.is_verified_spec(spec)
                && targets.has_target(
                    &fun_env,
                    &FunctionVariant::Verification(VerificationFlavor::Regular),
                )
            {                    
                println!("  - {}", fun_env.get_full_name_str());
            }
        }   
    }

    Ok(is_error)
}

pub async fn run_prover_module_mode(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<(bool, Buffer)> {
    let mut error_writer = Buffer::no_color();

    let error = run_prover_spec_no_abort_check(env, &mut error_writer, options, targets).await?;
    if error {
        return Ok((true, error_writer));
    }

    let error = run_prover_abort_check(env, &mut error_writer, options, targets).await?;
    if error {
        return Ok((true, error_writer));
    }

    let mut has_errors = false;

    let module_targets = targets
        .target_modules()
        .into_iter()
        .filter(|target| env.get_module(**target).is_target())
        .collect::<Vec<_>>();

    if options.remote.is_some() {
        for batch in module_targets.chunks(options.remote.as_ref().unwrap().concurrency) {
                let results = futures::future::join_all(
               batch.iter().map(|func| async {
                    let mut local_error_writer = Buffer::no_color();
                    let is_error = process_mod(env, &mut local_error_writer, options, *func).await;
                    (local_error_writer, is_error)
                })
            ).await;

            for (writer, is_error) in results {
                if is_error? {
                    has_errors = true;
                }
                error_writer.write(&writer.into_inner())?;
            }
        }
    } else {
        for mid in module_targets {
            let is_error = process_mod(env, &mut error_writer, options, mid).await?;
            if is_error {
                has_errors = true;
            }
        }
    }

    Ok((has_errors, error_writer))
}

pub fn check_errors<W: WriteColor>(
    env: &GlobalEnv,
    options: &Options,
    error_writer: &mut W,
    msg: String,
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
            boogie.call_remote_boogie_and_verify_output(&file_name, &options.remote.as_ref().unwrap()).await?;
        } else {
            boogie.call_boogie_and_verify_output(&file_name)?;
        }
    }

    Ok(())
}

/// Create bytecode and process it.
pub fn create_and_process_bytecode(
    options: &Options,
    env: &GlobalEnv,
    targets: &mut FunctionTargetsHolder,
) -> Option<String> {
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
        pipeline.run_with_dump(env, targets, &dump_file_base, options.prover.dump_cfg)
    } else {
        pipeline.run(env, targets)
    };

    // println!(
    //     "{}",
    //     mono_analysis::MonoInfoCFGDisplay {
    //         info: &mono_analysis::get_info(env),
    //         env
    //     }
    // );

    res.err().map(|p| p.name())
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
    let mut targets = FunctionTargetsHolder::new(Some(options.filter.clone()));
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
