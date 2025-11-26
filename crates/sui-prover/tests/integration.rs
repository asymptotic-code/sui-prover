use codespan_reporting::term::termcolor::Buffer;
use dir_test::{dir_test, Fixture};
use move_compiler::editions::Flavor;
use move_compiler::shared::known_attributes::ModeAttribute;
use move_package::BuildConfig as MoveBuildConfig;
use move_prover_boogie_backend::{
    generator::run_move_prover_with_model, generator_options::Options,
};
use regex::Regex;
use std::fs::{copy, create_dir_all, read_to_string};
use std::path::{Path, PathBuf};
use sui_prover::build_model::move_model_for_package_legacy;
use sui_prover::prove::DEFAULT_EXECUTION_TIMEOUT_SECONDS;

/// Runs the prover on the given file path and returns the output as a string
fn run_prover(file_path: &Path) -> String {
    let prover_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("packages")
        .join("sui-prover");
    let prover_dir_dis = prover_dir.display();
    let tmp = tempfile::tempdir().unwrap();
    let tmp_dir = tmp.path();
    std::fs::write(
        tmp_dir.join("Move.toml"),
        format!(
            r###"
[package]
name = "integration-test"
version = "0.0.1"
published-at = "0x2"
edition = "2024.beta"
[dependencies]
SuiProver = {{ local = "{prover_dir_dis}", override = true }}
[addresses]
integration-test = "0x9"
"###
        ),
    )
    .unwrap();
    let sources_dir = tmp_dir.join("sources");
    // create the sources_dir if it doesn't exist
    if !sources_dir.clone().exists() {
        create_dir_all(sources_dir.clone()).unwrap();
    }

    // Extract the relative path from tests/inputs/
    let relative_path = file_path
        .strip_prefix(Path::new("tests/inputs"))
        .unwrap_or_else(|_| Path::new(file_path.file_name().unwrap()));

    let extra_bpl_path = file_path
        .strip_prefix(Path::new("tests/inputs"))
        .map(|p| {
            Path::new("tests/extra_prelude")
                .join(p)
                .with_extension("bpl")
        })
        .unwrap_or(PathBuf::from("prelude_extra.bpl"));

    // Join it to the sources directory
    let new_file_path = sources_dir.join(relative_path);

    // Create parent directories if needed
    if let Some(parent_dir) = new_file_path.parent() {
        create_dir_all(parent_dir).unwrap();
    }

    // Copy the file
    copy(file_path, &new_file_path).unwrap();

    // Check if this is a conditionals test
    let is_conditionals_test = file_path
        .components()
        .any(|c| c.as_os_str().to_string_lossy() == "conditionals");

    // Setup cleanup that will execute even in case of panic or early return
    let result = std::panic::catch_unwind(|| {
        // Set up the build config
        let mut config = MoveBuildConfig::default();
        config.default_flavor = Some(Flavor::Sui);
        config.silence_warnings = false; // Disable warning suppression
        config.modes = vec![ModeAttribute::VERIFY_ONLY.into()];

        // Try to build the model
        let result = match move_model_for_package_legacy(config, tmp_dir) {
            Ok(model) => {
                // Create prover options
                let mut options = Options::default();
                options.backend.sequential_task = true;
                options.backend.use_array_theory = false; // we are not using them by default
                options.backend.vc_timeout = DEFAULT_EXECUTION_TIMEOUT_SECONDS;
                options.backend.prelude_extra = Some(extra_bpl_path);
                options.backend.debug_trace = false;
                options.backend.keep_artifacts = true;

                if is_conditionals_test {
                    options.prover.skip_spec_no_abort = true; // for better extracting of Boogie code
                    options.output_path = Path::new(&options.output_path)
                        .join("conditionals")
                        .join(file_path.file_name().unwrap())
                        .to_string_lossy()
                        .to_string();
                }

                // Use a buffer to capture output instead of stderr
                let mut error_buffer = Buffer::no_color();

                tokio::runtime::Runtime::new().unwrap().block_on(async {
                    // Run the prover with the buffer to capture all output
                    let prover_result = match run_move_prover_with_model(
                        &model,
                        &mut error_buffer,
                        options.clone(),
                        None,
                    )
                    .await
                    {
                        Ok(output) => {
                            let error_output =
                                String::from_utf8_lossy(&error_buffer.into_inner()).to_string();
                            format!("{output}\n{error_output}")
                        }
                        Err(err) => {
                            // Get the captured error output as string
                            let error_output =
                                String::from_utf8_lossy(&error_buffer.into_inner()).to_string();
                            format!("{}\n{}", err, error_output)
                        }
                    };

                    if is_conditionals_test {
                        // Extract and append Boogie code for conditional tests.
                        let boogie_code = extract_boogie_function(&options.output_path);
                        if !boogie_code.is_empty() {
                            format!(
                                "{}\n\n== Generated Boogie Code ==\n{}",
                                prover_result, boogie_code
                            )
                        } else {
                            prover_result
                        }
                    } else {
                        prover_result
                    }
                })
            }
            Err(err) => {
                // For model-building errors, we need to reformat the error to match the expected format
                format!("We hit an error: \n{}", err)
            }
        };

        post_process_output(result, sources_dir)
    });

    // Now handle the result of our operation
    match result {
        Ok(output) => output,
        Err(err) => format!(
            "Verification failed, panic during verification: {:?}",
            err.downcast_ref::<String>().unwrap_or(&String::new())
        ),
    }
}

fn post_process_output(output: String, sources_dir: PathBuf) -> String {
    // replace numbers such as 52571u64 with ELIDEDu64 to avoid snapshot diffs
    let output = output.replace(&format!("{}", sources_dir.display()), "tests/inputs");

    // make absolute paths referencing other packages (e.g. prover) relative
    let base_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let output = output.replace(&format!("{}", base_dir.display()), "tests/../../..");

    // Use regex to replace numbers with more than one digit followed by u64 with ELIDEDu64
    let re = Regex::new(r"\d{2,}u64").unwrap();
    re.replace_all(&output, "ELIDEDu64").to_string()
}

/// Helper for extracting boogie .bpl source: get implementation from file
fn extract_boogie_function(output_dir: &str) -> String {
    let output_path = Path::new(output_dir);

    // Try to find .bpl files in the output directory
    if let Ok(entries) = std::fs::read_dir(output_path) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().map_or(false, |ext| ext == "bpl") {
                if let Ok(content) = read_to_string(&path) {
                    // Look for both $impl and $pure functions
                    let functions = extract_impl_and_pure_functions(&content);
                    if !functions.is_empty() {
                        return functions.join("\n");
                    }
                }
            }
        }
    }

    String::new()
}

/// Helper for extracting boogie .bpl source: get $impl and $pure function bodies
fn extract_impl_and_pure_functions(bpl_content: &str) -> Vec<String> {
    let lines: Vec<&str> = bpl_content.lines().collect();
    let mut results = Vec::new();
    let mut in_target_function = false;
    let mut brace_count = 0;
    let mut function_lines = Vec::new();

    for line in lines {
        if (line.contains("$impl") || line.contains("$pure"))
            && (line.contains("procedure") || line.contains("function"))
        {
            in_target_function = true;
            function_lines.push(line);
        } else if in_target_function {
            function_lines.push(line);

            // Count braces :3
            for ch in line.chars() {
                match ch {
                    '{' => brace_count += 1,
                    '}' => {
                        brace_count -= 1;
                        if brace_count == 0 && !function_lines.is_empty() {
                            results.push(function_lines.join("\n"));
                            function_lines.clear();
                            in_target_function = false;
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    results
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/tests/inputs",
    glob: "**/*.move",
)]
fn move_test(fix: Fixture<&str>) {
    let absolute_path = fix.path().parse::<PathBuf>().unwrap();
    let move_path = absolute_path
        .strip_prefix(env!("CARGO_MANIFEST_DIR"))
        .unwrap();
    let output = run_prover(move_path);
    let filename = move_path.file_name().unwrap().to_string_lossy().to_string();
    let cp = move_path
        .parent()
        .unwrap()
        .components()
        .skip(2)
        .collect::<Vec<_>>();
    let cp_str = cp
        .iter()
        .map(|comp| comp.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<String>>();
    let snapshot_path = format!("snapshots/{}", cp_str.join("/"));
    insta::with_settings!({
        prepend_module_to_snapshot => false,
        snapshot_path => snapshot_path,
    }, {
        insta::assert_snapshot!(filename, output);
    });
}
