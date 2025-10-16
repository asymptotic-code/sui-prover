use itertools::Itertools;
use move_model::model::{FunctionEnv, GlobalEnv};
use termcolor::Buffer;
use std::path::{Path,PathBuf};
use move_package::{package_lock::PackageLock, source_package::layout::SourcePackageLayout, BuildConfig as MoveBuildConfig};
use move_stackless_bytecode::function_target_pipeline::{FunctionTargetPipeline, FunctionTargetsHolder};
use codespan_reporting::diagnostic::Severity;

use crate::{legacy_builder::ModelBuilderLegacy, prove::BuildConfig, system_dependencies::implicit_deps};

pub fn build_model(path: Option<&Path>, build_config: Option<BuildConfig>) -> Result<GlobalEnv, anyhow::Error> {
    let rerooted_path = reroot_path(path)?;
    let mut move_build_config = resolve_lock_file_path(
        build_config.unwrap_or_default().into(),
        Some(&rerooted_path),
    )?;

    move_build_config.implicit_dependencies = implicit_deps();

    move_model_for_package_legacy(
        move_build_config,
        &rerooted_path,
    )
}

pub fn move_model_for_package_legacy(
    config: MoveBuildConfig,
    path: &Path,
) -> Result<GlobalEnv, anyhow::Error> {
    let flags = config.compiler_flags();
    let resolved_graph = config.resolution_graph_for_package(path, None, &mut Buffer::no_color())?;
    let _mutx = PackageLock::lock(); // held until function returns

    ModelBuilderLegacy::create(resolved_graph).build_model(flags)
}

fn resolve_lock_file_path(
    mut build_config: MoveBuildConfig,
    package_path: Option<&Path>,
) -> Result<MoveBuildConfig, anyhow::Error> {
    if build_config.lock_file.is_none() {
        let package_root = reroot_path(package_path)?;
        let lock_file_path = package_root.join(SourcePackageLayout::Lock.path());
        build_config.lock_file = Some(lock_file_path);
    }
    Ok(build_config)
}

fn reroot_path(path: Option<&Path>) -> anyhow::Result<PathBuf> {
    let path = path
        .map(Path::canonicalize)
        .unwrap_or_else(|| PathBuf::from(".").canonicalize())?;
    // Always root ourselves to the package root, and then compile relative to that.
    let rooted_path = SourcePackageLayout::try_find_root(&path)?;
    std::env::set_current_dir(rooted_path)?;

    Ok(PathBuf::from("."))
}

#[allow(dead_code)] // This function is used in external cli
pub fn build_model_with_target(path: Option<&Path>) -> anyhow::Result<(GlobalEnv, PathBuf, FunctionTargetsHolder)> {
    let rerooted_path = reroot_path(path)?;
    let mut move_build_config = resolve_lock_file_path(
        BuildConfig::default().into(), 
        Some(&rerooted_path),
    )?;

    move_build_config.implicit_dependencies = implicit_deps();

    let model = move_model_for_package_legacy(
        move_build_config,
        &rerooted_path,
    )?;

    if model.has_errors() {
        let mut error_writer = Buffer::no_color();
        model.report_diag(&mut error_writer, Severity::Error);
        let diagnostic_output = String::from_utf8_lossy(&error_writer.into_inner()).to_string();
        return Err(anyhow::anyhow!("Move Model compiled with errors.\n{}", diagnostic_output));
    }

    let mut targets = FunctionTargetsHolder::new(Default::default(), None);

    for module in model.get_modules() {
        for func_env in module.get_functions() {
            targets.add_target(&func_env);
        }
    }

    Ok((model, rerooted_path, targets))
}

#[allow(dead_code)] // This function can be used in external cli
pub fn get_all_funs_in_topological_order<'env>(
    env: &'env GlobalEnv,
    targets: &'env FunctionTargetsHolder,
    only_targeted: bool,
) -> Vec<FunctionEnv<'env>> {
    let mut results = vec![];
    let graph = FunctionTargetPipeline::build_call_graph(env, targets);
    let sccs = petgraph::algo::kosaraju_scc(&graph);
    sccs.iter()
        .map(|scc| scc.iter().map(|node_idx| graph[*node_idx]).collect_vec())
        .for_each(|scc| {
            for qid in &scc {
                let fenv = env.get_function(*qid);
                if !only_targeted || fenv.module_env.is_target() {
                    results.push(fenv);
                }
            }
        });

    results
}
