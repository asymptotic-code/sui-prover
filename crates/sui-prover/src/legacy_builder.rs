// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use move_package::{
    compilation::compiled_package::{DependencyInfo, ModuleFormat, make_source_and_deps_for_compiler},
    resolution::resolution_graph::ResolvedGraph,
};
use anyhow::Result;
use itertools::Itertools;
use move_compiler::Flags;
use move_model::{
    model::GlobalEnv, options::ModelBuilderOptions,
    run_model_builder_with_options_and_compilation_flags,
};

#[derive(Debug, Clone)]
pub struct ModelBuilderLegacy {
    resolution_graph: ResolvedGraph,
}

impl ModelBuilderLegacy {
    pub fn create(resolution_graph: ResolvedGraph) -> Self {
        Self {
            resolution_graph,
        }
    }

    // NOTE: If there are now renamings, then the root package has the global resolution of all named
    // addresses in the package graph in scope. So we can simply grab all of the source files
    // across all packages and build the Move model from that.
    // TODO: In the future we will need a better way to do this to support renaming in packages
    // where we want to support building a Move model.
    pub fn build_model(&self, flags: Flags) -> Result<GlobalEnv> {
        // Make sure no renamings have been performed
        if let Some(pkg_name) = self.resolution_graph.contains_renaming() {
            anyhow::bail!(
                "Found address renaming in package '{}' when \
                    building Move model -- this is currently not supported",
                pkg_name
            )
        }

        // Targets are all files in the root package
        let root_name = self.resolution_graph.root_package();
        let root_package = self.resolution_graph.get_package(root_name).clone();
        let immediate_dependencies_names =
            root_package.immediate_dependencies(&self.resolution_graph);
        let deps_source_info = self
            .resolution_graph
            .package_table
            .iter()
            .filter_map(|(nm, pkg)| {
                if *nm == root_name {
                    return None;
                }
                let mut dep_source_paths = pkg
                    .get_sources(&self.resolution_graph.build_options)
                    .unwrap();
                let mut source_available = true;
                // If source is empty, search bytecode(mv) files
                if dep_source_paths.is_empty() {
                    dep_source_paths = pkg.get_bytecodes().unwrap();
                    source_available = false;
                }
                Some(Ok(DependencyInfo {
                    name: *nm,
                    is_immediate: immediate_dependencies_names.contains(nm),
                    source_paths: dep_source_paths,
                    address_mapping: &pkg.resolved_table,
                    compiler_config: pkg.compiler_config(
                        /* is_dependency */ true,
                        &self.resolution_graph.build_options,
                    ),
                    module_format: if source_available {
                        ModuleFormat::Source
                    } else {
                        ModuleFormat::Bytecode
                    },
                }))
            })
            .collect::<Result<Vec<_>>>()?;

        let (target, deps) = make_source_and_deps_for_compiler(
            &self.resolution_graph,
            &root_package,
            deps_source_info,
        )?;

        let all_targets = vec![target];
        let all_deps = deps.into_iter().map(|(p, _)| p).collect_vec();
        run_model_builder_with_options_and_compilation_flags(
            all_targets,
            all_deps,
            ModelBuilderOptions::default(),
            flags,
            None,
        )
    }
}
