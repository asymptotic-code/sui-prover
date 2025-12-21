// Copyright (c) Asymptotic Labs
// SPDX-License-Identifier: Apache-2.0

use std::fs;
use std::path::Path;

pub mod backend;
pub mod escape;
pub mod prelude;
pub mod renderer;
pub mod runtime;

// Re-exports for convenience
pub use backend::run_backend;

/// Writes the lakefile.lean for the project.
/// Note: lake-manifest.json is not generated - run `lake update` to create it with resolved dependencies.
pub fn write_lakefile(output_path: &Path, module_name: &str) -> anyhow::Result<()> {
    let lakefile_content = format!(
        r#"import Lake
open Lake DSL

-- interval brings in mathlib as a transitive dependency
require interval from git
  "https://github.com/girving/interval.git" @ "main"

package «{}» where
  -- add package configuration options here

lean_lib Prelude where
  roots := #[`Prelude]
  globs := #[.submodules `Prelude]

@[default_target]
lean_lib Impls where
  roots := #[`Impls]
  globs := #[.submodules `Impls]

@[default_target]
lean_lib Proofs where
  roots := #[`Proofs]
  globs := #[.submodules `Proofs]

@[default_target]
lean_lib Aborts where
  roots := #[`Aborts]
  globs := #[.submodules `Aborts]

@[default_target]
lean_lib Specs where
  roots := #[`Specs]
  globs := #[.submodules `Specs]
"#,
        module_name
    );

    fs::write(output_path.join("lakefile.lean"), lakefile_content)?;


    Ok(())
}
