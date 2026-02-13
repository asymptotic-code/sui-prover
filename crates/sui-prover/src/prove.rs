use crate::build_model::build_model;
use crate::llm_explain::explain_err;
use crate::remote_config::RemoteConfig;
use clap::Args;
use codespan_reporting::term::termcolor::Buffer;
use log::LevelFilter;
use move_compiler::editions::{Edition, Flavor};
use move_compiler::shared::known_attributes::ModeAttribute;
use move_core_types::account_address::AccountAddress;
use move_model::model::GlobalEnv;
use move_package::{BuildConfig as MoveBuildConfig, LintFlag};
use move_prover_boogie_backend::boogie_backend::options::BoogieFileMode;
use move_prover_boogie_backend::generator::{create_and_process_bytecode, run_boogie_gen};
use move_stackless_bytecode::function_stats;
use move_stackless_bytecode::function_target_pipeline::FunctionHolderTarget;
use move_stackless_bytecode::package_targets::PackageTargets;
use move_stackless_bytecode::spec_hierarchy;
use move_stackless_bytecode::target_filter::TargetFilterOptions;
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

impl From<BuildConfig> for MoveBuildConfig {
    fn from(config: BuildConfig) -> Self {
        Self {
            dev_mode: true,
            test_mode: false,
            json_errors: false,
            generate_docs: false,
            silence_warnings: true,
            warnings_are_errors: false,
            default_flavor: Some(Flavor::Sui),
            lint_flag: LintFlag::default(),
            install_dir: config.install_dir,
            force_recompilation: config.force_recompilation,
            lock_file: config.lock_file,
            fetch_deps_only: config.fetch_deps_only,
            skip_fetch_latest_git_deps: config.skip_fetch_latest_git_deps,
            default_edition: config.default_edition,
            deps_as_root: config.deps_as_root,
            additional_named_addresses: config.additional_named_addresses,
            save_disassembly: false,
            implicit_dependencies: BTreeMap::new(),
            modes: vec![ModeAttribute::VERIFY_ONLY.into()],
            force_lock_file: false,
        }
    }
}

/// General prove options
#[derive(Args)]
#[clap(next_help_heading = "General Options")]
pub struct GeneralConfig {
    /// Set verification timeout in seconds (default: 3000)
    #[clap(name = "timeout", long, short = 't', global = true)]
    pub timeout: Option<usize>,

    /// Force kill boogie process if boogie vc timeout is broken
    #[clap(name = "force-timeout", long, global = true)]
    pub force_timeout: bool,

    /// Don't delete temporary files after verification
    #[clap(name = "keep-temp", long, short = 'k', global = true)]
    pub keep_temp: bool,

    /// Only generate Boogie code, without running the prover
    #[clap(name = "generate-only", long, short = 'g', global = true)]
    pub generate_only: bool,

    /// Display detailed verification progress
    #[clap(name = "verbose", long, short = 'v', global = true)]
    pub verbose: bool,

    /// Don't display counterexample trace
    #[clap(name = "no-counterexample-trace", long, global = true)]
    pub no_counterexample_trace: bool,

    /// Explain the proving outputs via LLM
    #[clap(name = "explain", long, global = true)]
    pub explain: bool,

    /// Display detailed verification progress
    #[clap(name = "use_array_theory", long = "use_array_theory", global = true)]
    pub use_array_theory: bool,

    /// Split verification into separate proof goals for each execution path
    #[clap(name = "split-paths", long, short = 's', global = true)]
    pub split_paths: Option<usize>,

    /// Encode u8/u16/u32/u64/u128/u256 as bitvector instead of integer in boogie
    #[clap(name = "no-bv-int-encoding", long, global = true)]
    pub no_bv_int_encoding: bool,

    /// Boogie running mode
    #[clap(name = "boogie-file-mode", long, short = 'm', global = true,  default_value_t = BoogieFileMode::Function)]
    pub boogie_file_mode: BoogieFileMode,

    /// Dump bytecode to file
    #[clap(name = "dump-bytecode", long, short = 'd', global = true)]
    pub dump_bytecode: bool,

    /// Enable conditional merge insertion pass
    #[clap(name = "enable-conditional-merge-insertion", long, global = true)]
    pub enable_conditional_merge_insertion: bool,

    /// Skip checking spec functions that do not abort
    #[clap(name = "skip-spec-no-abort", long, global = true)]
    pub skip_spec_no_abort: bool,

    /// Skip checking external functions that do not abort
    #[clap(name = "skip-fun-no-abort", long, global = true)]
    pub skip_fun_no_abort: bool,

    /// Dump control-flow graphs to file
    #[clap(name = "stats", long, global = false)]
    pub stats: bool,

    /// Whether to enable CI mode for continuous integration environments
    #[clap(name = "ci", long, global = false)]
    pub ci: bool,

    /// Stream Boogie trace output in real time (passes -trace -traceverify to Boogie)
    #[clap(name = "trace", long, global = true)]
    pub trace: bool,
}

#[derive(Args, Default)]
#[clap(next_help_heading = "Build Options (subset of sui move build)")]
pub struct BuildConfig {
    /// Installation directory for compiled artifacts. Defaults to current directory.
    #[clap(long = "install-dir", global = true)]
    pub install_dir: Option<PathBuf>,

    /// Force recompilation of all packages
    #[clap(name = "force-recompilation", long = "force", global = true)]
    pub force_recompilation: bool,

    /// Optional location to save the lock file to, if package resolution succeeds.
    #[clap(skip)]
    pub lock_file: Option<PathBuf>,

    /// Only fetch dependency repos to MOVE_HOME
    #[clap(long = "fetch-deps-only", global = true)]
    pub fetch_deps_only: bool,

    /// Skip fetching latest git dependencies
    #[clap(long = "skip-fetch-latest-git-deps", global = true)]
    pub skip_fetch_latest_git_deps: bool,

    /// Default edition for move compilation, if not specified in the package's config
    #[clap(long = "default-move-edition", global = true)]
    pub default_edition: Option<Edition>,

    /// If set, dependency packages are treated as root packages. Notably, this will remove
    /// warning suppression in dependency packages.
    #[clap(long = "dependencies-are-root", global = true)]
    pub deps_as_root: bool,

    /// Additional named address mapping. Useful for tools in rust
    #[clap(skip)]
    pub additional_named_addresses: BTreeMap<String, AccountAddress>,
}

pub const DEFAULT_EXECUTION_TIMEOUT_SECONDS: usize = 45;

pub async fn execute(
    path: Option<&Path>,
    mut general_config: GeneralConfig,
    remote_config: RemoteConfig,
    build_config: BuildConfig,
    boogie_config: Option<String>,
    filter: TargetFilterOptions,
) -> anyhow::Result<()> {
    let model = build_model(path, Some(build_config))?;
    let package_targets = PackageTargets::new(&model, filter.clone(), !general_config.ci, None);

    general_config.skip_spec_no_abort = general_config.skip_spec_no_abort
        || package_targets.has_focus_specs()
        || filter.is_configured();

    if general_config.stats {
        function_stats::display_function_stats(&model, &package_targets);
        return Ok(());
    }

    let mut options = move_prover_boogie_backend::generator_options::Options::default();
    options.filter = filter.clone();
    let (targets, _) = create_and_process_bytecode(
        &options,
        &model,
        &package_targets,
        FunctionHolderTarget::All,
    );

    let output_dir = std::path::Path::new(&options.output_path);
    if !output_dir.exists() {
        std::fs::create_dir_all(output_dir)?;
    }
    spec_hierarchy::display_spec_hierarchy(&model, &targets, output_dir);

    execute_backend_boogie(model, &general_config, remote_config, boogie_config, filter).await
}

async fn execute_backend_boogie(
    model: GlobalEnv,
    general_config: &GeneralConfig,
    remote_config: RemoteConfig,
    boogie_config: Option<String>,
    filter: TargetFilterOptions,
) -> anyhow::Result<()> {
    let mut options = move_prover_boogie_backend::generator_options::Options::default();
    // don't spawn async tasks when running Boogie--causes a crash if we do
    options.backend.sequential_task = true;
    options.backend.use_array_theory = general_config.use_array_theory;
    options.backend.keep_artifacts = general_config.keep_temp;
    options.backend.vc_timeout = general_config
        .timeout
        .unwrap_or(DEFAULT_EXECUTION_TIMEOUT_SECONDS);
    options.backend.path_split = general_config.split_paths;
    options.prover.bv_int_encoding = !general_config.no_bv_int_encoding;
    options.backend.no_verify = general_config.generate_only;
    options.backend.bv_int_encoding = !general_config.no_bv_int_encoding;
    options.verbosity_level = if general_config.verbose {
        LevelFilter::Trace
    } else {
        LevelFilter::Info
    };
    options.backend.string_options = boogie_config;
    options.backend.boogie_file_mode = general_config.boogie_file_mode.clone();
    options.backend.debug_trace = !general_config.no_counterexample_trace;
    options.prover.debug_trace = !general_config.no_counterexample_trace;
    options.filter = filter;
    options.prover.dump_bytecode = general_config.dump_bytecode;
    options.prover.enable_conditional_merge_insertion =
        general_config.enable_conditional_merge_insertion;
    options.remote = remote_config.to_config()?;
    options.prover.skip_spec_no_abort = general_config.skip_spec_no_abort;
    options.prover.skip_fun_no_abort = general_config.skip_fun_no_abort;
    options.backend.force_timeout = general_config.force_timeout;
    options.backend.ci = general_config.ci;
    options.prover.ci = general_config.ci;
    options.backend.trace = general_config.trace;

    if general_config.explain {
        let mut error_writer = Buffer::no_color();
        match move_prover_boogie_backend::generator::run_move_prover_with_model(
            &model,
            &mut error_writer,
            options,
            None,
        )
        .await
        {
            Ok(_) => {
                let output = String::from_utf8_lossy(&error_writer.into_inner()).to_string();
                println!("Output: {}", output);
            }
            Err(e) => {
                let output = String::from_utf8_lossy(&error_writer.into_inner()).to_string();
                explain_err(&output, &e).await;
            }
        }
    } else {
        let result_str = run_boogie_gen(&model, options).await?;
        println!("{}", result_str)
    }

    Ok(())
}
