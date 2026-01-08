use std::{collections::BTreeMap, path::PathBuf, sync::LazyLock};

use move_package::source_package::parsed_manifest::{
    Dependencies, Dependency, DependencyKind, GitInfo, InternalDependency,
};

#[derive(Debug)]
pub struct SystemPackage {
    pub package_name: String,
    pub repo_path: String,
    pub local_dir_name: String, // Directory name when using local framework path
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
        git_revision: "next".to_owned(),
        packages: vec![
            SystemPackage {
                package_name: "MoveStdlib".to_owned(),
                repo_path: "crates/sui-framework/packages/move-stdlib".to_owned(),
                local_dir_name: "move-stdlib".to_owned(),
            },
            SystemPackage {
                package_name: "Sui".to_owned(),
                repo_path: "crates/sui-framework/packages/sui-framework".to_owned(),
                local_dir_name: "sui-framework".to_owned(),
            },
            SystemPackage {
                package_name: "SuiSystem".to_owned(),
                repo_path: "crates/sui-framework/packages/sui-system".to_owned(),
                local_dir_name: "sui-system".to_owned(),
            },
            SystemPackage {
                package_name: "DeepBook".to_owned(),
                repo_path: "crates/sui-framework/packages/deepbook".to_owned(),
                local_dir_name: "deepbook".to_owned(),
            },
        ],
    });

fn prover_deps() -> Dependencies {
    let mut deps: Dependencies = BTreeMap::new();

    // Check if we should use a local framework directory
    let local_framework_path = std::env::var("SUI_PROVER_FRAMEWORK_PATH").ok();

    if let Some(base_path) = &local_framework_path {
        // Try to find SuiProver in the local directory
        // Common names: sui-prover, SuiProver, prover
        for dir_name in ["sui-prover", "SuiProver", "prover"] {
            let local_path = PathBuf::from(base_path).join(dir_name);
            if local_path.exists() && local_path.join("Move.toml").exists() {
                let dep = Dependency::Internal(InternalDependency {
                    kind: DependencyKind::Local(local_path.to_string_lossy().to_string().into()),
                    subst: None,
                    digest: None,
                    dep_override: true,
                });

                deps.insert("SuiProver".to_string().into(), dep);
                return deps;
            }
        }

        // Return empty deps - don't load git-based SuiProver as it conflicts with custom stdlib
        return deps;
    }

    // Default: use git-based dependency
    let dep = Dependency::Internal(InternalDependency {
        kind: DependencyKind::Git(GitInfo {
            git_url: SYSTEM_PROVER_GIT_REPO.into(),
            git_rev: "main".to_string().into(),
            subdir: "packages/sui-prover".to_string().into(),
        }),
        subst: None,
        digest: None,
        dep_override: true,
    });

    deps.insert("SuiProver".to_string().into(), dep);

    deps
}

fn system_deps() -> Dependencies {
    // Check if we should use a local framework directory instead of git
    let local_framework_path = std::env::var("SUI_PROVER_FRAMEWORK_PATH").ok();

    if let Some(base_path) = &local_framework_path {
        let base_path = PathBuf::from(base_path);
        let system_deps = LATEST_SYSTEM_PACKAGES
            .packages
            .iter()
            .filter_map(|package| {
                let local_path = base_path.join(&package.local_dir_name);

                // Check if the directory exists
                if !local_path.exists() {
                    return None;
                }

                // Check if it has a Move.toml
                if !local_path.join("Move.toml").exists() {
                    return None;
                }

                let dep = Dependency::Internal(InternalDependency {
                    kind: DependencyKind::Local(local_path.to_string_lossy().to_string().into()),
                    subst: None,
                    digest: None,
                    dep_override: true,
                });

                Some((package.package_name.clone().into(), dep))
            })
            .collect();

        return system_deps;
    }

    // Default: use git-based dependencies
    let system_deps = LATEST_SYSTEM_PACKAGES
        .packages
        .iter()
        .map(|package| {
            let dep = Dependency::Internal(InternalDependency {
                kind: DependencyKind::Git(GitInfo {
                    git_url: SYSTEM_SUI_GIT_REPO.into(),
                    git_rev: LATEST_SYSTEM_PACKAGES.git_revision.clone().into(),
                    subdir: package.repo_path.clone().into(),
                }),
                subst: None,
                digest: None,
                dep_override: true,
            });

            (package.package_name.clone().into(), dep)
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
