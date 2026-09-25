use std::{
    collections::{BTreeMap, HashSet},
    path::{Path, PathBuf},
    sync::LazyLock,
};

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

// The named addresses each implicit system package brings into the build. A
// package that assigns one of these names differently -- or claims it as its
// own with 0x0, as a repository shipping its own `deepbook` does -- conflicts
// with the injected copy ("Conflicting assignments for address"). Such a
// package IS that system package (or its own fork of it), so the injected copy
// is left out. `system_packages_are_all_mapped` pins this to `implicit_deps()`.
const SYSTEM_PACKAGE_ADDRESSES: &[(&str, &[(&str, &str)])] = &[
    ("MoveStdlib", &[("std", "0x1")]),
    ("Sui", &[("sui", "0x2")]),
    ("SuiSystem", &[("sui_system", "0x3")]),
    ("DeepBook", &[("deepbook", "0xdee9")]),
    ("SuiProver", &[("prover", "0x0"), ("specs", "0x0")]),
];

// Injected even when their addresses look claimed. A spec package
// conventionally declares `specs = "0x0"` for itself, the name sui-specs also
// binds at 0x0; leaving SuiProver out there removes `prover::prover` and
// `specs::*` from exactly the packages that need them.
const NEVER_SKIPPED: &[&str] = &["SuiProver"];

/// `implicit_deps()` without the system packages the package at `root` owns
/// an address of (see `SYSTEM_PACKAGE_ADDRESSES`).
pub fn implicit_deps_for(root: &Path) -> Dependencies {
    let owned = conflicting_system_packages(root);
    let mut deps = implicit_deps();
    deps.retain(|name, _| !owned.contains(name.as_str()));
    deps
}

fn parse_address(value: &str) -> Option<u128> {
    let hex = value.trim().strip_prefix("0x")?;
    let digits = hex.trim_start_matches('0');
    if digits.is_empty() {
        return Some(0);
    }
    if digits.len() > 32 {
        return None;
    }
    u128::from_str_radix(digits, 16).ok()
}

/// Two assignments of one named address clash unless they name the same
/// non-zero address: 0x0 means "this package's own address", so two packages
/// both claiming a name are two different packages. An assignment that does
/// not parse (a placeholder `_`) is treated as a clash.
fn addresses_clash(ours: &str, system: &str) -> bool {
    match (parse_address(ours), parse_address(system)) {
        (Some(a), Some(b)) => a != b || a == 0,
        _ => true,
    }
}

/// Every named address assigned by the package at `root` and by the packages
/// it reaches through `local` dependencies (regular and dev), with the value
/// each assigns. A manifest that does not parse contributes nothing.
fn declared_addresses(root: &Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut seen: HashSet<PathBuf> = HashSet::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let dir = dir.canonicalize().unwrap_or(dir);
        if !seen.insert(dir.clone()) {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(dir.join("Move.toml")) else {
            continue;
        };
        let Ok(doc) = text.parse::<toml::Table>() else {
            continue;
        };
        for section in ["addresses", "dev-addresses"] {
            if let Some(table) = doc.get(section).and_then(|t| t.as_table()) {
                for (name, value) in table {
                    if let Some(v) = value.as_str() {
                        out.push((name.clone(), v.to_string()));
                    }
                }
            }
        }
        for section in ["dependencies", "dev-dependencies"] {
            if let Some(table) = doc.get(section).and_then(|t| t.as_table()) {
                for dep in table.values() {
                    if let Some(local) = dep.get("local").and_then(|l| l.as_str()) {
                        stack.push(dir.join(local));
                    }
                }
            }
        }
    }
    out
}

/// The implicit system packages the package at `root` clashes with: it (or a
/// local dependency) assigns one of their named addresses differently.
fn conflicting_system_packages(root: &Path) -> HashSet<String> {
    let declared = declared_addresses(root);
    SYSTEM_PACKAGE_ADDRESSES
        .iter()
        .filter(|(pkg, _)| !NEVER_SKIPPED.contains(pkg))
        .filter(|(_, addrs)| {
            addrs.iter().any(|(name, value)| {
                declared
                    .iter()
                    .any(|(n, v)| n == name && addresses_clash(v, value))
            })
        })
        .map(|(pkg, _)| pkg.to_string())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{
        addresses_clash, conflicting_system_packages, implicit_deps, SYSTEM_PACKAGE_ADDRESSES,
    };
    use std::collections::HashSet;
    use std::path::Path;

    fn write(root: &Path, rel: &str, text: &str) {
        let p = root.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    }

    #[test]
    fn system_packages_are_all_mapped() {
        let mapped: HashSet<&str> = SYSTEM_PACKAGE_ADDRESSES.iter().map(|(p, _)| *p).collect();
        for name in implicit_deps().keys() {
            assert!(
                mapped.contains(name.as_str()),
                "implicit system package {name} has no entry in SYSTEM_PACKAGE_ADDRESSES"
            );
        }
    }

    #[test]
    fn only_a_different_or_owned_assignment_clashes() {
        assert!(!addresses_clash("0x2", "0x2"));
        assert!(!addresses_clash(
            "0x0000000000000000000000000000000000000000000000000000000000000002",
            "0x2"
        ));
        assert!(addresses_clash("0x0", "0xdee9"));
        assert!(addresses_clash("0x0", "0x0"));
        assert!(addresses_clash("_", "0x2"));
    }

    #[test]
    fn a_package_owning_deepbook_skips_only_deepbook() {
        let tmp = std::env::temp_dir().join(format!("sp-sysaddr-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        write(&tmp, "deepbook/Move.toml", "[package]\nname = \"deepbook\"\n[dependencies]\ntoken = { local = \"../token\" }\n[addresses]\ndeepbook = \"0x0\"\n");
        write(
            &tmp,
            "token/Move.toml",
            "[package]\nname = \"token\"\n[addresses]\ntoken = \"0x0\"\nsui = \"0x2\"\n",
        );
        write(&tmp, "account/Move.toml", "[package]\nname = \"account\"\n[dependencies]\ndeepbook = { local = \"../deepbook\" }\n[addresses]\naccount = \"0x0\"\n");
        let only_deepbook: HashSet<String> = ["DeepBook".to_string()].into();
        assert_eq!(
            conflicting_system_packages(&tmp.join("deepbook")),
            only_deepbook
        );
        assert_eq!(
            conflicting_system_packages(&tmp.join("account")),
            only_deepbook
        );
        assert!(conflicting_system_packages(&tmp.join("token")).is_empty());
        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn a_spec_package_keeps_the_prover() {
        let tmp = std::env::temp_dir().join(format!("sp-specpkg-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        write(
            &tmp,
            "deepbook/Move.toml",
            "[package]\nname = \"deepbook\"\n[addresses]\ndeepbook = \"0x0\"\n",
        );
        write(&tmp, "specs/Move.toml", "[package]\nname = \"specs\"\n[dependencies]\ndeepbook = { local = \"../deepbook\" }\n[addresses]\nspecs = \"0x0\"\nprover = \"0x0\"\n");
        let only_deepbook: HashSet<String> = ["DeepBook".to_string()].into();
        assert_eq!(
            conflicting_system_packages(&tmp.join("specs")),
            only_deepbook
        );
        let _ = std::fs::remove_dir_all(&tmp);
    }
}
