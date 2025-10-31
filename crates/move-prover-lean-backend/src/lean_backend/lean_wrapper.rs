use crate::lean_backend::options::LeanOptions;
use anyhow::anyhow;
use bimap::BiBTreeMap;
use itertools::Itertools;
use log::{debug, info};
use move_model::code_writer::CodeWriter;
use move_model::model::{GlobalEnv, Loc};
use move_model::ty::Type;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;
use std::fs;
use crate::lean_backend::prover_task_runner::{ProverTaskRunner, RunLeanWithSeeds};

/// This file is nearly identical to Boogie's boogie_wrapper.rs, with minor var name changes.

/// Represents the lean wrapper.
pub struct LeanWrapper<'env> {
    pub env: &'env GlobalEnv,
    pub targets: &'env FunctionTargetsHolder,
    pub writer: &'env CodeWriter,
    pub options: &'env LeanOptions,
    pub types: &'env BiBTreeMap<Type, String>,
}

/// Output of a lean run.
pub struct LeanOutput {
    /// All errors which could be parsed from the output.
    pub errors: Vec<LeanError>,

    /// Full output as a string.
    pub all_output: String,
}

/// A lean error.
#[derive(Debug)]
pub struct LeanError {
    pub loc: Loc,
    pub message: String,
}

impl LeanWrapper<'_> {
    /// Calls lean on the given file. On success, returns a struct representing the analyzed
    /// output of lean.
    pub async fn call_lean(&self, lean_file: &str) -> anyhow::Result<LeanOutput> {
        let args = self.options.get_lean_command(lean_file)?;
        info!("running solver");
        debug!("command line: {}", args.iter().join(" "));
        let mut task = RunLeanWithSeeds {
            options: self.options.clone(),
            lean_file: lean_file.to_string(),
        };
        // When running on complicated formulas(especially those with quantifiers), SMT solvers
        // can suffer from the so-called butterfly effect, where minor changes such as using
        // different random seeds cause significant instabilities in verification times.
        // Thus by running multiple instances of Lean with different random seeds, we can
        // potentially alleviate the instability.
        // TODO determine if Lean uses seeded random.
        let (seed, output_res) = if self.options.sequential_task {
            let seed = 0;
            (seed, task.run_sync(seed))
        } else {
            ProverTaskRunner::run_tasks(
                task,
                self.options.num_instances,
                self.options.sequential_task,
                self.options.hard_timeout_secs,
            ).await
        };
        let output = match output_res {
            Err(err) => {
                if err.kind() == std::io::ErrorKind::TimedOut {
                    let err = LeanError {
                        loc: self.env.unknown_loc(),
                        message: format!(
                            "Lean execution exceeded hard timeout of {}s",
                            self.options.hard_timeout_secs
                        ),
                    };
                    return Ok(LeanOutput {
                        errors: vec![err],
                        all_output: "".to_string(),
                    });
                } else {
                    panic!("cannot execute lean `{:?}`: {}", args, err)
                }
            }
            Ok(out) => out,
        };
        if self.options.num_instances > 1 {
            debug!("Lean instance with seed {} finished first", seed);
        }

        debug!("analyzing lean output");
        let out = String::from_utf8_lossy(&output.stdout).to_string();
        let err = String::from_utf8_lossy(&output.stderr).to_string();
        // TODO parse output
        let mut errors = vec![];
        Ok(LeanOutput {
            errors,
            all_output: out,
        })
    }

    /// Calls lean and analyzes output.
    pub async fn call_lean_and_verify_output(&self, lean_file: &str) -> anyhow::Result<()> {
        let LeanOutput { errors, all_output } = self.call_lean(lean_file).await?;
        let lean_log_file = self.options.get_lean_log_file(lean_file);
        let log_file_existed = std::path::Path::new(&lean_log_file).exists();
        debug!("writing lean log to {}", lean_log_file);
        fs::write(&lean_log_file, &all_output)?;

        for error in &errors {
            println!("Error: {error:?}");
        }

        if !log_file_existed && !self.options.keep_artifacts {
            std::fs::remove_file(lean_log_file).unwrap_or_default();
        }

        Ok(())
    }
}
