use std::path::{Path, PathBuf};

use move_model::model::GlobalEnv;
use move_package::package_lock::PackageLock;
use move_package::source_package::layout::SourcePackageLayout;
use move_package::BuildConfig as MoveBuildConfig;
use termcolor::Buffer;

use crate::package_resolution_graph::resolution_graph_for_package;
use crate::legacy_builder::ModelBuilderLegacy;
use crate::prove::BuildConfig;
use move_stackless_bytecode::function_target_pipeline::FunctionTargetsHolder;

pub fn move_model_for_package_legacy(
    config: MoveBuildConfig,
    path: &Path,
) -> Result<GlobalEnv, anyhow::Error> {
    let flags = config.compiler_flags();
    let resolved_graph = resolution_graph_for_package(config, path, None, &mut Buffer::no_color())?;
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
    std::env::set_current_dir(rooted_path).unwrap();

    Ok(PathBuf::from("."))
}

pub fn build_model(path: Option<&Path>, build_config: BuildConfig) -> anyhow::Result<GlobalEnv> {
    let rerooted_path = reroot_path(path)?;
    let move_build_config = resolve_lock_file_path(
        build_config.into(), 
        Some(&rerooted_path),
    )?;

    move_model_for_package_legacy(
        move_build_config,
        &rerooted_path,
    )
}

pub fn build_model_with_target(path: Option<&Path>) -> anyhow::Result<(GlobalEnv, PathBuf, FunctionTargetsHolder)> {
    let rerooted_path = reroot_path(path)?;
    let move_build_config = resolve_lock_file_path(
        BuildConfig::default().into(), 
        Some(&rerooted_path),
    )?;

    let model = move_model_for_package_legacy(
        move_build_config,
        &rerooted_path,
    )?;

    let mut targets = FunctionTargetsHolder::new();

    for module in model.get_modules() {
        for func_env in module.get_functions() {
            targets.add_target(&func_env);
        }
    }

    Ok((model, rerooted_path, targets))
}
