use log::LevelFilter;
use move_stackless_bytecode::options::ProverOptions;
use serde::{Deserialize, Serialize};

/// Represents options provided to the tool. Most of those options are configured via a toml
/// source; some over the command line flags.
///
/// NOTE: any fields carrying structured data must appear at the end for making
/// toml printing work. When changing this config, use `mvp --print-config` to
/// verify this works.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct Options {
    /// The path to the lean output which represents the verification problem.
    pub output_path: String,
    /// Verbosity level for logging.
    pub verbosity_level: LevelFilter,
    /// The paths to the Move sources.
    pub move_sources: Vec<String>,
    /// The paths to any dependencies for the Move sources. Those will not be verified but
    /// can be used by `move_sources`.
    pub move_deps: Vec<String>,
    /// The values assigned to named addresses in the Move code being verified.
    pub move_named_address_values: Vec<String>,
    /// Whether to run experimental pipeline
    pub experimental_pipeline: bool,

    /// BEGIN OF STRUCTURED OPTIONS. DO NOT ADD VALUE FIELDS AFTER THIS
    /// Options for the prover.
    pub prover: ProverOptions,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            output_path: "output".to_string(),
            verbosity_level: LevelFilter::Info,
            move_sources: vec![],
            move_deps: vec![],
            move_named_address_values: vec![],
            prover: ProverOptions::default(),
            experimental_pipeline: false,
        }
    }
}
