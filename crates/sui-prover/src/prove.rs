use crate::legacy_builder::ModelBuilderLegacy;
use crate::llm_explain::explain_err;
use crate::package_resolution_graph::resolution_graph_for_package;
use clap::{Args, ValueEnum};
use codespan_reporting::term::termcolor::Buffer;
use log::LevelFilter;
use move_compiler::editions::{Edition, Flavor};
use move_core_types::account_address::AccountAddress;
use move_model::model::GlobalEnv;
use move_package::{
    package_lock::PackageLock, source_package::layout::SourcePackageLayout,
    BuildConfig as MoveBuildConfig, LintFlag,
};
use std::{
    collections::BTreeMap
    ,
    path::{Path, PathBuf},
};
use std::fmt::{Display, Formatter};
use move_prover_boogie_backend::{
    generator::run_boogie_gen,
    generator_options::BoogieFileMode,
};

pub fn move_model_for_package_legacy(
    config: MoveBuildConfig,
    path: &Path,
) -> Result<GlobalEnv, anyhow::Error> {
    let flags = config.compiler_flags();
    let resolved_graph = resolution_graph_for_package(config, path, None, &mut Buffer::no_color())?;
    let _mutx = PackageLock::lock(); // held until function returns

    ModelBuilderLegacy::create(resolved_graph).build_model(flags)
}

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
            modes: vec![ModeAttribute::VERIFY_ONLY.into(), ModeAttribute::TEST_ONLY.into(), ModeAttribute::TEST.into()],
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

    /// Don't delete temporary files after verification
    #[clap(name = "keep-temp", long, short = 'k', global = true)]
    pub keep_temp: bool,

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

    /// Lean running mode
    #[clap(name = "backend", long, global = true, default_value_t = BackendOptions::Boogie)]
    pub backend: BackendOptions,

    /// Dump bytecode to file
    #[clap(name = "dump-bytecode", long, short = 'd', global = true)]
    pub dump_bytecode: bool,
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

#[derive(ValueEnum, Default, Clone)]
pub enum BackendOptions {
    #[default]
    Boogie,
    Lean
}

impl Display for BackendOptions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BackendOptions::Boogie => write!(f, "boogie"),
            BackendOptions::Lean => write!(f, "lean"),
        }
    }
}

pub async fn execute(
    path: Option<&Path>,
    general_config: GeneralConfig,
    build_config: BuildConfig,
    boogie_config: Option<String>,
    filter: TargetFilterOptions,
) -> anyhow::Result<()> {
    let rerooted_path = reroot_path(path)?;
    let move_build_config = resolve_lock_file_path(build_config.into(), Some(&rerooted_path))?;

    let model = move_model_for_package_legacy(move_build_config, &rerooted_path)?;

    if matches!(general_config.backend, BackendOptions::Boogie) {
        execute_backend_boogie(model, &general_config, boogie_config).await
    } else {
        execute_backend_lean(model, &general_config).await
    }
}

async fn execute_backend_boogie(
    model: GlobalEnv,
    general_config: &GeneralConfig,
    boogie_config: Option<String>,
) -> anyhow::Result<()> {
    let model = build_model(path, Some(build_config))?;
    let mut options = move_prover_boogie_backend::generator_options::Options::default();
    // don't spawn async tasks when running Boogie--causes a crash if we do
    options.backend.sequential_task = true;
    options.backend.use_array_theory = general_config.use_array_theory;
    options.backend.keep_artifacts = general_config.keep_temp;
    options.backend.vc_timeout = general_config.timeout.unwrap_or(3000);
    options.backend.path_split = general_config.split_paths;
    options.prover.bv_int_encoding = !general_config.no_bv_int_encoding;
    options.backend.bv_int_encoding = !general_config.no_bv_int_encoding;
    options.verbosity_level = if general_config.verbose { LevelFilter::Trace } else { LevelFilter::Info };
    options.backend.string_options = boogie_config;
    options.backend.boogie_file_mode = general_config.boogie_file_mode;
    options.backend.debug_trace = !general_config.no_counterexample_trace;
    options.filter = filter;
    options.prover.dump_bytecode = general_config.dump_bytecode;

    if general_config.explain {
        let mut error_writer = Buffer::no_color();
        match move_prover_boogie_backend::generator::run_move_prover_with_model(&model, &mut error_writer, options, None) {
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
       let result_str = run_boogie_gen(&model, options)?;
       println!("{}", result_str)
    }

    Ok(())
}

async fn execute_backend_lean(
    model: GlobalEnv,
    general_config: &GeneralConfig) -> anyhow::Result<()> {
    let mut options = move_prover_lean_backend::generator_options::Options::default();
    options.verbosity_level = if general_config.verbose {
        LevelFilter::Trace
    } else {
        LevelFilter::Info
    };
    let mut error_writer = Buffer::no_color();
    match move_prover_lean_backend::generator::run_move_prover_with_model(options, &model, &mut error_writer) {
        Ok(_) => {
            let output = String::from_utf8_lossy(&error_writer.into_inner()).to_string();
            println!("Output: {}", output);
        }
        Err(e) => {
            let output = String::from_utf8_lossy(&error_writer.into_inner()).to_string();
            explain_err(&output, &e).await;
        }
    }
    Ok(())
}
