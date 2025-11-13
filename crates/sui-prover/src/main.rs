use std::path::PathBuf;

use clap::*;
use colored::Colorize;
use move_stackless_bytecode::target_filter::TargetFilterOptions;
use prove::{execute, BuildConfig, GeneralConfig};
use remote_config::RemoteConfig;
use tracing::debug;

mod build_model;
mod legacy_builder;
mod llm_explain;
mod prompts;
mod prove;
mod remote_config;
mod system_dependencies;

#[derive(Parser)]
#[clap(
    name = env!("CARGO_BIN_NAME"),
    about = "Command-line tool for formal verification of Move code within Sui projects. When executed from the project's root directory, it attempts to prove all specifications annotated with #[spec(prove)]",
    rename_all = "kebab-case",
    author,
    version = env!("CARGO_PKG_VERSION"),
)]
pub struct Args {
    /// Path to package directory with a Move.toml inside
    #[clap(long = "path", short = 'p', global = true)]
    pub package_path: Option<PathBuf>,

    /// Boggie options
    #[clap(long = "boogie-config", short = 'b', global = true)]
    pub boogie_config: Option<String>,

    /// General options
    #[clap(flatten)]
    pub general_config: GeneralConfig,

    /// Package build options
    #[clap(flatten)]
    pub build_config: BuildConfig,

    /// Filtering options
    #[clap(flatten)]
    pub filter_config: TargetFilterOptions,

    /// Remote prover options
    #[clap(flatten)]
    pub remote_config: RemoteConfig,
}

#[tokio::main]
async fn main() {
    #[cfg(windows)]
    colored::control::set_virtual_terminal(true).unwrap();

    let bin_name = env!("CARGO_BIN_NAME");
    let args = Args::parse();

    let _guard = telemetry_subscribers::TelemetryConfig::new("sui-prover")
        .with_log_file(&format!("{bin_name}.log"))
        .with_log_level("debug")
        .with_env()
        .init();

    debug!("Sui-Prover CLI version: {}", env!("CARGO_PKG_VERSION"));

    let result = if args.remote_config.cloud_config_create {
        args.remote_config.create()
    } else {
        execute(
            args.package_path.as_deref(),
            args.general_config,
            args.remote_config,
            args.build_config,
            args.boogie_config,
            args.filter_config,
        )
        .await
    };

    match result {
        Ok(_) => (),
        Err(err) => {
            let err = format!("{:?}", err);
            println!("{}", err.bold().red());
            std::process::exit(1);
        }
    }
}
