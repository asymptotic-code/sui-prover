/// This file is nearly identical to Boogie's generator.rs, with minor var name changes.
use std::cell::RefCell;
use crate::generator_options::Options;
use anyhow::anyhow;
use codespan_reporting::diagnostic::Severity;
use codespan_reporting::term::termcolor::WriteColor;
use log::info;
use move_model::model::GlobalEnv;
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetsHolder, FunctionVariant, VerificationFlavor};
use move_stackless_bytecode::number_operation::GlobalNumberOperationState;
use move_stackless_bytecode::pipeline_factory;
use std::fs;
use std::path::Path;
use bimap::BiBTreeMap;
use move_model::code_writer::CodeWriter;
use move_model::ty::Type;
use crate::add_prelude;
use crate::lean_backend::bytecode_translator::LeanTranslator;
use crate::lean_backend::lean_wrapper::LeanWrapper;

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

pub fn run_move_prover_with_model<W: WriteColor>(
    options: Options,
    env: &GlobalEnv,
    error_writer: &mut W,
) -> anyhow::Result<()> {
    env.report_diag(error_writer, options.prover.report_severity);
    env.set_extension(options.prover.clone());
    create_init_num_operation_state(env);

    let (targets, _err_processor) = create_and_process_bytecode(&options, env);

    check_errors(
        env,
        &options,
        error_writer,
        // TODO: add _err_processor to this message
        "exiting with bytecode transformation errors",
    )?;

    let output_path = Path::new(&options.output_path);
    let output_existed = output_path.exists();

    if !output_existed {
        fs::create_dir_all(output_path)?;
    }
    
    let has_errors = run_prover_function_mode(env, error_writer, &options, &targets)?;

    if has_errors {
        return Err(anyhow!("exiting with verification errors"));
    }
    
    Ok(())
}

pub fn run_prover_function_mode<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    options: &Options,
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<bool> {
    let mut has_errors = false;

    for target in targets.specs() {
        if !env.get_function(*target).module_env.is_target() || !targets.is_verified_spec(target) {
            continue;
        }

        let fun_env = env.get_function(*target);
        let has_target = targets.has_target(
            &env.get_function(*target),
            &FunctionVariant::Verification(VerificationFlavor::Regular),
        );
        let file_name = fun_env.get_full_name_str();

        if has_target {
            println!("🔄 {file_name}");
        }

        let new_targets = FunctionTargetsHolder::for_one_spec(target, targets.clone());
        let (code_writer, types) = generate_lean(env, &options, &new_targets)?;

        check_errors(
            env,
            &options,
            error_writer,
            "exiting with condition generation errors",
        )?;

        verify_lean(env, &options, &new_targets, code_writer, types, file_name.clone())?;

        let is_error = env.has_errors();
        env.report_diag(error_writer, options.prover.report_severity);

        if is_error {
            has_errors = true;
        }

        if has_target {
            if is_error {
                println!("❌ {file_name}");
            } else {
                print!("\x1B[1A\x1B[2K");
                println!("✅ {file_name}");
            }
        }
    }

    Ok(has_errors)
}

pub fn generate_lean(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
) -> anyhow::Result<(CodeWriter, BiBTreeMap<Type, String>)> {
    let writer = CodeWriter::new(env.internal_loc());
    let types = RefCell::new(BiBTreeMap::new());
    add_prelude(env, &options.backend, &writer)?;
    let mut translator = LeanTranslator::new(env, &options.backend, targets, &writer, &types);
    translator.translate();
    Ok((writer, types.into_inner()))
}

pub fn verify_lean(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
    writer: CodeWriter,
    types: BiBTreeMap<Type, String>,
    target_name: String,
) -> anyhow::Result<()> {
    let file_name = format!("{}/{}.lean", options.output_path, target_name);

    writer.process_result(|result| if cfg!(target_os = "windows") {
        fs::write(&file_name.replace("::", "_"), result)
    } else {
        fs::write(&file_name, result)
    })?;

    if !options.prover.generate_only {
        let lean = LeanWrapper {
            env,
            targets,
            options: &options.backend,
            writer: &writer,
            types: &types,
        };
        lean.call_lean_and_verify_output(&file_name)?;
    }

    Ok(())
}

pub fn create_and_process_bytecode(
    options: &Options,
    env: &GlobalEnv,
) -> (FunctionTargetsHolder, Option<String>) {
    let mut targets = FunctionTargetsHolder::new(None);
    let output_dir = Path::new(&options.output_path)
        .parent()
        .expect("expect the parent directory of the output path to exist");
    let output_prefix = options.move_sources.first().map_or("bytecode", |s| {
        Path::new(s).file_name().unwrap().to_str().unwrap()
    });

    let dump_dir = options
        .move_sources
        .first()
        .map(|s| Path::new(s))
        .map(|p| if p.is_file() { p.parent().unwrap_or(Path::new(".")) } else { p })
        .unwrap_or(Path::new("."));

    if options.prover.dump_bytecode {
        fs::create_dir_all(dump_dir).expect("create dump directory");
    }

    // Add function targets for all functions in the environment.
    for module_env in env.get_modules() {
        if module_env.is_target() {
            info!("preparing module {}", module_env.get_full_name_str());
        }
        if options.prover.dump_bytecode {
            let dump_file = dump_dir.join(format!("{}.mv.disas", output_prefix));
            fs::write(&dump_file, module_env.disassemble()).expect("dumping disassembled module");
        }
        for func_env in module_env.get_functions() {
            targets.add_target(&func_env)
        }
    }

    // Create processing pipeline and run it.
    let pipeline = if options.experimental_pipeline {
        pipeline_factory::experimental_pipeline()
    } else {
        pipeline_factory::default_pipeline_with_options(&options.prover)
    };

    let res = if options.prover.dump_bytecode {
        let dump_file_base = dump_dir
            .join(output_prefix)
            .into_os_string()
            .into_string()
            .unwrap();
        pipeline.run_with_dump(env, &mut targets, &dump_file_base, options.prover.dump_cfg)
    } else {
        pipeline.run(env, &mut targets)
    };

    // println!(
    //     "{}",
    //     mono_analysis::MonoInfoCFGDisplay {
    //         info: &mono_analysis::get_info(env),
    //         env
    //     }
    // );

    (targets, res.err().map(|p| p.name()))
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
