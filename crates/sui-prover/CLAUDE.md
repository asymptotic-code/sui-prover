# CLAUDE.md - sui-prover

CLI entry point and orchestration for the Sui Prover formal verification tool.

## Overview

This crate provides the command-line interface for verifying Move smart contracts. It orchestrates model building, analysis pipeline execution, and Boogie backend verification.

**Entry point**: `main.rs` → `prove.rs::execute()`

## Directory Structure

```
src/
├── main.rs                # CLI entry point (clap-based argument parsing)
├── lib.rs                 # Public module exports
├── prove.rs               # Core prover execution logic
├── build_model.rs         # Move model building from source
├── remote_config.rs       # Cloud verification configuration
├── system_dependencies.rs # Implicit framework dependencies
├── legacy_builder.rs      # Legacy model builder wrapper
├── llm_explain.rs         # Optional LLM-based error explanation
└── prompts.rs             # LLM prompt templates
tests/
├── integration.rs         # Snapshot test framework
├── inputs/                # Test .move files (32 categories)
└── snapshots/             # Expected test outputs
```

## Key CLI Options

```bash
sui-prover --path ./project     # Specify package path
sui-prover --timeout 60         # Verification timeout (seconds)
sui-prover --verbose            # Detailed output
sui-prover --generate-only      # Generate Boogie without verifying
sui-prover --keep-temp          # Keep temporary .bpl files
sui-prover --skip-spec-no-abort # Skip spec no-abort checking
sui-prover --skip-fun-no-abort  # Skip function no-abort checking
sui-prover --cloud              # Use remote cloud verification
sui-prover --dump-bytecode      # Output bytecode to file
```

## Key Functions

### prove.rs
- `execute()` - Main entry point, builds model and runs verification
- `GeneralConfig` - All general verification options
- `BuildConfig` - Move compilation and dependency options

### build_model.rs
- `build_model(path, config)` - Public API to build GlobalEnv from Move source
- `build_model_with_target(path)` - Returns (GlobalEnv, path, FunctionTargetsHolder)
- `get_all_funs_in_topological_order()` - Dependency-ordered function list

### remote_config.rs
- `CloudConfig` - Remote server configuration (URL, API key, concurrency)
- `RemoteConfig::create()` - Interactive cloud setup
- Config stored at `$HOME/.asymptotic/sui_prover.toml`

### system_dependencies.rs
- `implicit_deps()` - Default framework dependencies (Sui, MoveStdlib, etc.)
- `SystemPackagesVersion` - Git revision tracking for dependencies

## Testing

Tests use `insta` for snapshot testing with `dir_test` for auto-discovery.

**Test naming**: `move_test__{category}_{filename}` (e.g., `move_test__axioms_simple_ok`)

**Test file conventions**:
- `.ok.move` - Expected to pass verification
- `.fail.move` - Expected to fail verification

**Workflow**:
```bash
cargo test -p sui-prover                    # Run tests, creates .snap.new for changes
cargo insta review                          # Review diffs interactively
cargo insta test -p sui-prover --accept     # Auto-accept all changes
```

## Test Categories

`tests/inputs/` contains 32 test categories:
- `axioms/`, `pure_functions/`, `opaque/` - Function spec features
- `ghost/`, `inv/`, `loop_invariant/` - Advanced specifications
- `dynamic_field/`, `object/`, `table/` - Sui data structures
- `vector/`, `option/`, `vec_map/`, `vec_set/` - Collections
- `quantifiers/`, `scenario/`, `conditionals/` - Language features

## Adding a New Test

1. Add `.ok.move` or `.fail.move` file to `tests/inputs/{category}/`
2. Run `cargo test -p sui-prover`
3. Review with `cargo insta review`
4. Accept changes

## Environment Variables

- `SUI_PROVER_FRAMEWORK_PATH` - Override local framework path
- `OPENAI_API_KEY` - Required for `--explain` LLM feature

## Important Notes

- Model building uses `PackageLock` for thread-safety (except in tests)
- Implicit dependencies (Sui framework) are automatically resolved
- The `--cloud` option requires prior configuration via `--cloud-config`
- Default timeout is 45 seconds per verification task