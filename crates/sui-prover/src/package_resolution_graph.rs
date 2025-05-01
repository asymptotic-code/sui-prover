// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use anyhow::Context;
use colored::Colorize;
use move_symbol_pool::Symbol;
use move_package::{
    lock_file::{schema, LockFile}, package_hooks::custom_resolve_pkg_id, package_lock::PackageLock, resolution::{
        dependency_graph::{
            DependencyGraph, 
            DependencyGraphBuilder, DependencyGraphInfo, DependencyMode,
        }, 
        resolution_graph::ResolvedGraph,
    }, source_package::{
        layout::SourcePackageLayout, 
        manifest_parser::{
            parse_move_manifest_string,
            parse_source_manifest
        }, 
        parsed_manifest::{
            Dependencies, 
            Dependency, 
            DependencyKind, 
            GitInfo, 
            InternalDependency,
        }
    }, BuildConfig
};
use petgraph::prelude::DiGraphMap;
use termcolor::WriteColor;
use std::{collections::{BTreeMap, BTreeSet}, fs::File, path::{Path, PathBuf}};
use sha2::{Digest, Sha256};

fn prover_deps() -> Dependencies {
    let mut res: Dependencies = BTreeMap::new();
    res.insert(
    "SuiProver".to_string().into(),
    Dependency::Internal(InternalDependency {
            kind: DependencyKind::Git(GitInfo {
                git_url: "https://github.com/asymptotic-code/sui-prover.git".to_string().into(),
                git_rev: "main".to_string().into(),
                subdir: "packages/sui-prover".to_string().into(),
            }),
            subst: None,
            digest: None,
            dep_override: true,
        }),
    );

    res
}

pub fn resolution_graph_for_package<W: WriteColor>(
    mut config: BuildConfig,
    path: &Path,
    chain_id: Option<String>,
    writer: &mut W,
) -> Result<ResolvedGraph, anyhow::Error> {
    if config.test_mode {
        config.dev_mode = true;
    }
    let path = SourcePackageLayout::try_find_root(path)?;
    let manifest_string =
        std::fs::read_to_string(path.join(SourcePackageLayout::Manifest.path()))?;
    let lock_path = path.join(SourcePackageLayout::Lock.path());
    let lock_string = std::fs::read_to_string(lock_path.clone()).ok();
    let _mutx = PackageLock::lock(); // held until function returns

    let install_dir_set = config.install_dir.is_some();
    let install_dir = config.install_dir.as_ref().unwrap_or(&path).to_owned();

    let mut dep_graph_builder = DependencyGraphBuilder::new(
        config.skip_fetch_latest_git_deps,
        writer,
        install_dir.clone(),
        config.implicit_dependencies.clone(),
    );
    let (dependency_graph, modified) = get_graph(
        &mut dep_graph_builder,
        DependencyKind::default(),
        path,
        manifest_string,
        lock_string,
        Some(prover_deps()),
    )?;

    if modified || install_dir_set {
        // (1) Write the Move.lock file if the existing one is `modified`, or
        // (2) `install_dir` is set explicitly, which may be a different directory, and where a Move.lock does not exist yet.
        let lock = dependency_graph.write_to_lock(install_dir, Some(lock_path))?;
        if let Some(lock_path) = &config.lock_file {
            lock.commit(lock_path)?;
        }
    }

    let DependencyGraphBuilder {
        mut dependency_cache,
        progress_output,
        ..
    } = dep_graph_builder;

    ResolvedGraph::resolve(
        dependency_graph,
        config,
        &mut dependency_cache,
        chain_id,
        progress_output,
    )
}

fn get_graph<W: WriteColor>(
    dgb: &mut DependencyGraphBuilder<W>,
    parent: DependencyKind,
    root_path: PathBuf,
    manifest_string: String,
    lock_string_opt: Option<String>,
    additional_deps: Option<Dependencies>,
) -> Result<(DependencyGraph, bool), anyhow::Error> {
    let toml_manifest = parse_move_manifest_string(manifest_string.clone())?;
    let mut root_manifest = parse_source_manifest(toml_manifest)?;

    if additional_deps.is_some() {
        root_manifest.dependencies.extend(additional_deps.unwrap());
    }

    // compute digests eagerly as even if we can't reuse existing lock file, they need to become
    // part of the newly computed dependency graph
    let new_manifest_digest = digest_str(manifest_string.into_bytes().as_slice());
    let lock_path = root_path.join(SourcePackageLayout::Lock.path());
    let lock_file = File::open(lock_path);
    let digest_and_lock_contents = lock_file
        .map(|mut lock_file| match schema::Header::read(&mut lock_file) {
            Ok(header) if header.version < schema::VERSION => None, // outdated lock file - regenerate
            Ok(header) => Some((header.manifest_digest, header.deps_digest, lock_string_opt)),
            Err(_) => None, // malformed header - regenerate lock file
        })
        .unwrap_or(None);

    // implicits deps should be skipped if the manifest contains any of them
    // explicitly (or if the manifest is for a system package).
    let explicit_implicits: Vec<&Symbol> = dgb
        .implicit_deps
        .keys()
        .filter(|name| root_manifest.dependencies.contains_key(name))
        .collect();

    let is_implicit: bool = dgb.implicit_deps.contains_key(&root_manifest.package.name);

    if !is_implicit && explicit_implicits.is_empty() {
        for (name, dep) in dgb.implicit_deps.iter() {
            root_manifest.dependencies.insert(*name, dep.clone());
        }
    } else if !is_implicit && parent == DependencyKind::default() {
        eprintln!(
            "[{}] Dependencies on {} are automatically added, but this feature is \
            disabled for your package because you have explicitly included dependencies on {}. Consider \
            removing these dependencies from {}.",
            "note".bold().yellow(),
            move_compiler::format_oxford_list!("and", "{}", dgb.implicit_deps.keys().collect::<Vec<_>>()),
            move_compiler::format_oxford_list!("and", "{}", explicit_implicits),
            SourcePackageLayout::Manifest.location_str(),
        );
    }

    // collect sub-graphs for "regular" and "dev" dependencies
    let root_pkg_id = custom_resolve_pkg_id(&root_manifest).with_context(|| {
        format!(
            "Resolving package name for '{}'",
            root_manifest.package.name
        )
    })?;

    let root_pkg_name = root_manifest.package.name;
    let (mut dep_graphs, resolved_id_deps, mut dep_names, mut overrides) = dgb
        .collect_graphs(
            &parent,
            root_pkg_id,
            root_pkg_name,
            root_path.clone(),
            DependencyMode::Always,
            root_manifest.dependencies.clone(),
        )?;
    let dep_lock_files = dep_graphs
        .values()
        // write_to_lock should create a fresh lockfile for computing the dependency digest, hence the `None` arg below
        .map(|graph_info| graph_info.g.write_to_lock(dgb.install_dir.clone(), None))
        .collect::<Result<Vec<LockFile>, _>>()?;
    let (dev_dep_graphs, dev_resolved_id_deps, dev_dep_names, dev_overrides) = dgb
        .collect_graphs(
            &parent,
            root_pkg_id,
            root_pkg_name,
            root_path.clone(),
            DependencyMode::DevOnly,
            root_manifest.dev_dependencies.clone(),
        )?;

    // compute new digests and return early if the manifest and deps digests are unchanged
    let dev_dep_lock_files = dev_dep_graphs
        .values()
        // write_to_lock should create a fresh lockfile for computing the dependency digest, hence the `None` arg below
        .map(|graph_info| graph_info.g.write_to_lock(dgb.install_dir.clone(), None))
        .collect::<Result<Vec<LockFile>, _>>()?;
    let new_deps_digest = dgb.dependency_digest(dep_lock_files, dev_dep_lock_files)?;
    let (manifest_digest, deps_digest) = match digest_and_lock_contents {
        Some((old_manifest_digest, old_deps_digest, Some(lock_string)))
            if old_manifest_digest == new_manifest_digest
                && old_deps_digest == new_deps_digest =>
        {
            return Ok((
                DependencyGraph::read_from_lock(
                    root_path,
                    root_pkg_id,
                    root_pkg_name,
                    &mut lock_string.as_bytes(), // safe since old_deps_digest exists
                    None,
                )?,
                false,
            ));
        }
        _ => (new_manifest_digest, new_deps_digest),
    };

    // combine the subgraphs for the dependencies into a single graph for the root package
    dep_graphs.extend(dev_dep_graphs);
    dep_names.extend(dev_dep_names);

    let mut combined_graph = DependencyGraph {
        root_path,
        root_package_id: root_pkg_id,
        root_package_name: root_pkg_name,
        package_graph: DiGraphMap::new(),
        package_table: BTreeMap::new(),
        always_deps: BTreeSet::new(),
        manifest_digest,
        deps_digest,
    };
    // ensure there's always a root node, even if it has no edges
    combined_graph
        .package_graph
        .add_node(combined_graph.root_package_id);

    for (
        dep_id,
        DependencyGraphInfo {
            g,
            mode,
            is_override,
            is_external: _,
            version: _,
        },
    ) in dep_graphs.iter_mut()
    {
        g.prune_subgraph(
            root_pkg_name,
            *dep_id,
            *dep_names.get(dep_id).unwrap(),
            *is_override,
            *mode,
            &overrides,
            &dev_overrides,
        )?;
    }

    let mut all_deps = resolved_id_deps;
    all_deps.extend(dev_resolved_id_deps);

    // we can mash overrides together as the sets cannot overlap (it's asserted during pruning)
    overrides.extend(dev_overrides);

    combined_graph.merge(
        dep_graphs,
        &parent,
        &all_deps,
        &overrides,
        &dep_names,
        root_pkg_name,
    )?;

    combined_graph.check_acyclic()?;
    combined_graph.discover_always_deps();

    Ok((combined_graph, true))
}

pub fn digest_str(data: &[u8]) -> String {
    format!("{:X}", Sha256::digest(data))
}
