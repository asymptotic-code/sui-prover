use std::{collections::BTreeMap, sync::LazyLock};

use move_package::source_package::parsed_manifest::{
    Dependencies, Dependency, DependencyKind, GitInfo, InternalDependency,
};

#[derive(Debug)]
pub struct SystemPackage {
    pub package_name: String,
    pub repo_path: String,
}

#[derive(Debug)]
pub struct SystemPackagesVersion {
    pub git_revision: String,
    pub packages: Vec<SystemPackage>,
}

static SYSTEM_SUI_GIT_REPO: &str = "https://github.com/asymptotic-code/sui.git";
static SYSTEM_PROVER_GIT_REPO: &str = "https://github.com/asymptotic-code/sui-prover.git";

static LATEST_SYSTEM_PACKAGES: LazyLock<SystemPackagesVersion> =
    LazyLock::new(|| SystemPackagesVersion {
        git_revision: "next_new".to_owned(),
        packages: vec![
            SystemPackage {
                package_name: "MoveStdlib".to_owned(),
                repo_path: "crates/sui-framework/packages/move-stdlib".to_owned(),
            },
            SystemPackage {
                package_name: "Sui".to_owned(),
                repo_path: "crates/sui-framework/packages/sui-framework".to_owned(),
            },
            SystemPackage {
                package_name: "SuiSystem".to_owned(),
                repo_path: "crates/sui-framework/packages/sui-system".to_owned(),
            },
            SystemPackage {
                package_name: "DeepBook".to_owned(),
                repo_path: "crates/sui-framework/packages/deepbook".to_owned(),
            },
        ],
    });

fn prover_deps() -> Dependencies {
    let mut deps: Dependencies = BTreeMap::new();
    deps.insert(
        "SuiProver".to_string().into(),
        Dependency::Internal(InternalDependency {
            kind: DependencyKind::Git(GitInfo {
                git_url: SYSTEM_PROVER_GIT_REPO.into(),
                git_rev: "new-sui-version".to_string().into(),
                subdir: "packages/sui-prover".to_string().into(),
            }),
            subst: None,
            digest: None,
            dep_override: true,
        }),
    );

    deps
}

fn system_deps() -> Dependencies {
    let system_deps = LATEST_SYSTEM_PACKAGES
        .packages
        .iter()
        .map(|package| {
            (
                package.package_name.clone().into(),
                Dependency::Internal(InternalDependency {
                    kind: DependencyKind::Git(GitInfo {
                        git_url: SYSTEM_SUI_GIT_REPO.into(),
                        git_rev: LATEST_SYSTEM_PACKAGES.git_revision.clone().into(),
                        subdir: package.repo_path.clone().into(),
                    }),
                    subst: None,
                    digest: None,
                    dep_override: true,
                }),
            )
        })
        .collect();

    system_deps
}

pub fn implicit_deps() -> Dependencies {
    let mut deps: Dependencies = BTreeMap::new();
    deps.extend(system_deps());
    deps.extend(prover_deps());
    deps
}
