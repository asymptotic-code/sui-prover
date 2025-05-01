// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

use move_package::source_package::parsed_manifest::{Dependencies, Dependency, DependencyKind, GitInfo, InternalDependency};
use std::collections::BTreeMap;

pub fn prover_implicit_deps() -> Dependencies {
    let mut res: Dependencies = BTreeMap::new();
    res.insert(
    "SuiProver".to_string().into(),
    Dependency::Internal(InternalDependency {
            kind: DependencyKind::Git(GitInfo {
                git_url: "https://github.com/asymptotic-code/sui-prover.git".to_string().into(),
                git_rev: "dependencies-wip".to_string().into(),
                subdir: "packages/sui-prover".to_string().into(),
            }),
            subst: None,
            digest: None,
            dep_override: true,
        }),
    );
    
    res
}
