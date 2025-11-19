use crate::add_prelude;
use crate::generator_options::Options;
use crate::lean_backend::bytecode_translator::LeanTranslator;
use crate::lean_backend::lean_wrapper::LeanWrapper;
use anyhow::anyhow;
use bimap::BiBTreeMap;
use codespan_reporting::term::termcolor::WriteColor;
use log::info;
use move_model::code_writer::CodeWriter;
use move_model::model::GlobalEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_stats::PackageTargets;
use move_stackless_bytecode::function_target_pipeline::{
    FunctionHolderTarget, FunctionTargetsHolder,
};
use move_stackless_bytecode::number_operation::GlobalNumberOperationState;
use move_stackless_bytecode::options::ProverOptions;
use move_stackless_bytecode::pipeline_factory;
/// This file is nearly identical to Boogie's generator.rs, with minor var name changes.
use std::cell::RefCell;
use std::fs;
use std::path::Path;

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

pub async fn run_move_prover_with_model<W: WriteColor>(
    options: Options,
    env: &GlobalEnv,
    error_writer: &mut W,
) -> anyhow::Result<()> {
    env.report_diag(error_writer, options.prover.report_severity);

    let output_path = Path::new(&options.output_path);
    let output_existed = output_path.exists();

    if !output_existed {
        fs::create_dir_all(output_path)?;
    }

    let has_errors = run_prover_function_mode(env, error_writer, &options).await?;

    if has_errors {
        return Err(anyhow!("exiting with verification errors"));
    }

    Ok(())
}

pub async fn run_prover_function_mode<W: WriteColor>(
    env: &GlobalEnv,
    error_writer: &mut W,
    options: &Options,
) -> anyhow::Result<bool> {
    let mut has_errors = false;

    let package_targets = PackageTargets::new(&env, Default::default(), options.prover.ci);
    for target in &package_targets.target_specs {
        env.cleanup();

        let file_name = env.get_function(*target).get_full_name_str();
        println!("🔄 {}", file_name);

        let (targets, _) = create_and_process_bytecode(
            options,
            env,
            &package_targets,
            FunctionHolderTarget::Function(*target),
        );
        check_errors(
            env,
            &options,
            error_writer,
            // TODO: add _err_processor to this message
            "exiting with bytecode transformation errors",
        )?;

        let (code_writer, types) = generate_lean(env, options, &targets)?;
        check_errors(
            env,
            &options,
            error_writer,
            "exiting with condition generation errors",
        )?;

        verify_lean(
            env,
            &options,
            &targets,
            code_writer,
            types,
            file_name.clone(),
        )
        .await?;

        let is_error = env.has_errors();
        env.report_diag(error_writer, options.prover.report_severity);

        if is_error {
            has_errors = true;
        }

        if is_error {
            println!("❌ {file_name}");
        } else {
            print!("\x1B[1A\x1B[2K");
            println!("✅ {file_name}");
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

pub async fn verify_lean(
    env: &GlobalEnv,
    options: &Options,
    targets: &FunctionTargetsHolder,
    writer: CodeWriter,
    types: BiBTreeMap<Type, String>,
    target_name: String,
) -> anyhow::Result<()> {
    let file_name = format!("{}/{}.lean", options.output_path, target_name);

    writer.process_result(|result| {
        if cfg!(target_os = "windows") {
            fs::write(&file_name.replace("::", "_"), result)
        } else {
            fs::write(&file_name, result)
        }
    })?;

    if !options.prover.generate_only {
        let lean = LeanWrapper {
            env,
            targets,
            options: &options.backend,
            writer: &writer,
            types: &types,
        };
        lean.call_lean_and_verify_output(&file_name).await?;
    }

    Ok(())
}

pub fn create_and_process_bytecode(
    options: &Options,
    env: &GlobalEnv,
    package_targets: &PackageTargets,
    target_type: FunctionHolderTarget,
) -> (FunctionTargetsHolder, Option<String>) {
    // Populate initial number operation state for each function and struct based on the pragma
    create_init_num_operation_state(env, &options.prover);

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
