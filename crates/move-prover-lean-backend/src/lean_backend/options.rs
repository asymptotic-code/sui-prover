use std::collections::HashSet;
use std::path::PathBuf;
use move_command_line_common::env::read_env_var;
use serde::{Deserialize, Serialize};

/// Default flags passed to lean. Additional flags will be added to this via the -B option.
const DEFAULT_LEAN_FLAGS: &[&str] = &[];

/// Lean options.
/// TODO clean up old Boogie options if they're not used
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(default, deny_unknown_fields)]
pub struct LeanOptions {
    /// Path to the lean executable.
    pub lean_exe: String,
    /// Path to the z3 executable.
    pub z3_exe: String,
    /// Whether to use cvc5.
    pub use_cvc5: bool,
    /// Path to the cvc5 executable.
    pub cvc5_exe: String,
    /// Whether to generate debug trace code.
    pub debug_trace: bool,
    /// List of flags to pass on to lean.
    pub lean_flags: Vec<String>,
    /// Whether to use native array theory.
    pub use_array_theory: bool,
    /// Whether to produce an SMT file for each verification problem.
    pub generate_smt: bool,
    /// Whether native instead of stratified equality should be used.
    pub native_equality: bool,
    /// A string determining the type of requires used for parameter type checks. Can be
    /// `"requires"` or `"free requires`".
    pub type_requires: String,
    /// The depth until which stratified functions are expanded.
    pub stratification_depth: usize,
    /// A string to be used to inline a function of medium size. Can be empty or `{:inline}`.
    pub aggressive_func_inline: String,
    /// A string to be used to inline a function of small size. Can be empty or `{:inline}`.
    pub func_inline: String,
    /// A bound to apply to the length of serialization results.
    pub serialize_bound: usize,
    /// How many times to call the prover backend for the verification problem. This is used for
    /// benchmarking.
    pub bench_repeat: usize,
    /// Whether to use the sequence theory as the internal representation for $Vector type.
    pub vector_using_sequences: bool,
    /// A seed for the prover.
    pub random_seed: usize,
    /// The number of cores to use for parallel processing of verification conditions.
    pub proc_cores: usize,
    /// A (soft) timeout for the solver, per verification condition, in seconds.
    pub vc_timeout: usize,
    /// Whether Lean output and log should be saved.
    pub keep_artifacts: bool,
    /// Eager threshold for quantifier instantiation.
    pub eager_threshold: usize,
    /// Lazy threshold for quantifier instantiation.
    pub lazy_threshold: usize,
    /// Whether to use the new Lean `{:debug ..}` attribute for tracking debug values.
    pub stable_test_output: bool,
    /// Number of Lean instances to be run concurrently.
    pub num_instances: usize,
    /// Whether to run Lean instances sequentially.
    pub sequential_task: bool,
    /// A hard timeout for lean execution; if the process does not terminate within
    /// this time frame, it will be killed. Zero for no timeout.
    pub hard_timeout_secs: u64,
    /// Whether to generate a z3 trace file and where to put it.
    pub z3_trace_file: Option<String>,
    /// Number of iterations to unroll loops.
    pub loop_unroll: Option<u64>,
    pub prelude_extra: Option<PathBuf>,
    pub path_split: Option<usize>,
    /// All possible additional options as simle string
    pub string_options: Option<String>,
}

impl Default for LeanOptions {
    fn default() -> Self {
        Self {
            bench_repeat: 1,
            lean_exe: read_env_var("LEAN_EXE"),
            z3_exe: read_env_var("Z3_EXE"),
            use_cvc5: false,
            cvc5_exe: read_env_var("CVC5_EXE"),
            lean_flags: vec![],
            debug_trace: false,
            use_array_theory: false,
            generate_smt: false,
            native_equality: false,
            type_requires: "free requires".to_owned(),
            stratification_depth: 6,
            aggressive_func_inline: "".to_owned(),
            func_inline: "{:inline}".to_owned(),
            serialize_bound: 0,
            vector_using_sequences: false,
            random_seed: 1,
            proc_cores: 4,
            vc_timeout: 40,
            keep_artifacts: true,
            eager_threshold: 100,
            lazy_threshold: 100,
            stable_test_output: false,
            num_instances: 1,
            sequential_task: false,
            hard_timeout_secs: 0,
            z3_trace_file: None,
            loop_unroll: None,
            prelude_extra: Some(PathBuf::from("prelude_extra.lean")),
            path_split: Some(10),
            string_options: None,
        }
    }
}

impl LeanOptions {

    /// Returns command line to call lean.
    pub fn get_lean_command(&self, lean_file: &str) -> anyhow::Result<Vec<String>> {
        let mut result = vec![self.lean_exe.clone()];

        // If we don't have a lean executable, try using the path default one
        if result.iter().all(|path| path.is_empty()) {
            result = vec!["lean".to_string()];
        }

        // Set to track unique options
        let mut seen_options = HashSet::new();
        let mut add = |sl: &[&str]| {
            for s in sl {
                seen_options.insert(s.to_string());
            }
        };

        add(DEFAULT_LEAN_FLAGS);

        for f in &self.lean_flags {
            add(&[f.as_str()]);
        }

        add(&[lean_file]);

        let additional_options = self.string_options
            .as_deref()
            .map(|s| s.split(' ').map(|opt| format!("-{}", opt)).collect())
            .unwrap_or_else(Vec::new);

        add(&additional_options.iter().map(|s| s.as_str()).collect::<Vec<&str>>());

        result.extend(seen_options.into_iter());

        Ok(result)
    }

    /// Returns name of file where to log lean output.
    pub fn get_lean_log_file(&self, lean_file: &str) -> String {
        format!("{}.log", lean_file)
    }
}