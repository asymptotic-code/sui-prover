# CLAUDE.md

This file provides guidance to Claude Code when working with the sui-prover codebase.

## Project Overview

Sui Prover is a formal verification tool for Move smart contracts on the Sui blockchain. It uses the Boogie verification engine and the Z3 SMT solver.

**Pipeline**: Move Source → GlobalEnv (move-model) → Stackless Bytecode → Analysis Passes → Boogie Code → Z3 → Verification Result

## Crate Structure

```
crates/
├── sui-prover/                    # CLI entry point and orchestration
├── move-model/                    # Semantic model of Move code (GlobalEnv, types, AST)
├── move-stackless-bytecode/       # Bytecode transformation and 30+ analysis passes
├── move-prover-boogie-backend/    # Boogie code generation and solver execution
└── lambda-boogie-handler/         # AWS Lambda wrapper for remote verification
```

### sui-prover (CLI)
- Entry point: `src/main.rs` → `src/prove.rs::execute()`
- Handles CLI args, model building, pipeline orchestration
- Key files: `prove.rs`, `build_model.rs`, `remote_config.rs`

### move-model
- Builds semantic model from Move source
- Key types: `GlobalEnv`, `ModuleEnv`, `FunctionEnv`, `StructEnv`, `Loc`, `Type`
- Core file: `src/model.rs` (2000+ lines)

### move-stackless-bytecode
- Transforms Move bytecode to stackless form
- Runs 30+ analysis passes (verification, loop, liveness, borrow, etc.)
- Key types: `FunctionTarget`, `FunctionTargetsHolder`, `PackageTargets`
- Key file: `src/function_target_pipeline.rs`

### move-prover-boogie-backend
- Translates stackless bytecode to Boogie verification conditions
- Key files: `src/boogie_backend/bytecode_translator.rs`, `spec_translator.rs`
- Prelude templates in `src/boogie_backend/prelude/`

## Essential Commands

### Building
```bash
cargo build -p sui-prover

# Install from source
cargo install --locked --path ./crates/sui-prover
```

**Note:** Don't use `-p move-model` directly - there's a name conflict with a git dependency. Building `sui-prover` pulls in all local crates.

### Running the Prover
```bash
# Basic usage (run from directory with Move.toml)
sui-prover

# Common options
sui-prover --path ./my_project    # Specify package path
sui-prover --timeout 60           # Set verification timeout (seconds)
sui-prover --verbose              # Detailed output
sui-prover --generate-only        # Generate Boogie without verifying
sui-prover --keep-temp            # Keep temporary .bpl files
sui-prover --skip-spec-no-abort   # Skip spec no-abort checking
sui-prover --skip-fun-no-abort    # Skip fun no-abort checking (`#[ext(no_abort)]` or `#[ext(pure)]`)
```

### Testing
```bash
# Run all sui-prover tests
cargo test -p sui-prover

# Run tests matching a pattern (e.g., all axiom tests)
cargo test -p sui-prover -- axioms

# Run a specific test file (tests are named move_test__{filename without .move})
cargo test -p sui-prover -- move_test__axioms_simple_ok
```

### Snapshot Testing (Important!)
Tests use `insta` for snapshot testing. Test inputs are in `crates/sui-prover/tests/inputs/` and snapshots in `crates/sui-prover/tests/snapshots/`.

```bash
# Run tests (creates .snap.new files for any changes)
cargo test -p sui-prover

# Run a specific test (test names: move_test__{category}_{filename})
cargo test -p sui-prover -- move_test__dynamic_field_issue_237

# Review snapshot changes interactively (shows diff, prompts accept/reject)
cargo insta test -p sui-prover --review

# Auto-accept all snapshot changes
cargo insta test -p sui-prover --accept

# Review pending .snap.new files without re-running tests
cargo insta review
```

**Workflow when tests fail due to snapshot mismatch:**
1. Run `cargo test -p sui-prover` - creates `.snap.new` files for changes
2. Run `cargo insta review` to see diffs and accept/reject each change

**Note:** `.snap.new` files in git status indicate pending snapshot reviews.

### Linting
```bash
cargo fmt --all -- --check
cargo check --all-targets --all-features
```

**Important:** Always run `cargo fmt --all` before committing code changes.

## Architecture

### Data Flow
```
Move Source (.move files)
    ↓
GlobalEnv (move-model) - semantic model with types, functions, specs
    ↓
Stackless Bytecode (move-stackless-bytecode) - transformed bytecode
    ↓
Analysis Pipeline - 30+ passes (verification, loop, liveness, borrow, etc.)
    ↓
FunctionTarget - annotated bytecode with analysis results
    ↓
Boogie Code (move-prover-boogie-backend) - verification conditions
    ↓
Z3 (via Boogie) - SMT solving
    ↓
Verification Result - success, failure with counterexamples, or timeout
```

### Key Types

**GlobalEnv** (move-model): Root environment containing all modules, symbol pool, diagnostics
```rust
// Access patterns
let module_env = global_env.get_module(module_id);
let func_env = module_env.get_function(func_id);
let struct_env = module_env.get_struct(struct_id);
```

**FunctionTarget** (move-stackless-bytecode): Function with bytecode and analysis annotations
```rust
// Created by FunctionTargetPipeline after running analysis passes
let target = targets.get_target(&func_env, &FunctionVariant::Baseline);
```

**PackageTargets** (move-stackless-bytecode): Selects which functions to verify based on `#[spec(prove)]`

**Options** (move-prover-boogie-backend): All configuration (prover, boogie, filtering, remote)

### Specification Syntax
Functions to verify are marked with `#[spec(prove)]`:
```move
#[spec(prove)]
fun my_function_spec(args): ReturnType {
    requires(precondition);
    let result = my_function(args);
    ensures(postcondition);
    result
}
```

## Testing Patterns

### Snapshot Tests
- Test inputs: `crates/sui-prover/tests/inputs/**/*.move`
- Snapshots: `crates/sui-prover/tests/snapshots/`
- Test categories: axioms, conditionals, dynamic_field, ghost, inv, loop_invariant, object, opaque, pure_functions, quantifiers, scenario, etc.

### Adding a New Test
1. Add `.move` file to appropriate category in `tests/inputs/`
2. Run `cargo test -p sui-prover`
3. Review generated snapshot with `cargo insta test -p sui-prover --review`

### Test Post-Processing
Snapshots are normalized to remove:
- Absolute paths
- Non-deterministic numeric values
- Temporary directory references

## System Dependencies

The prover requires external tools (assumed to be installed):
- **Z3** - SMT solver
- **Boogie** - Verification condition generator

## Common Workflows

### Debugging a Verification Failure
1. Run with `--verbose` to see detailed output
2. Use `--keep-temp` to inspect generated Boogie files
3. Check the `.bpl` file for the generated verification conditions
4. Look for counterexample output in verification failures

### Adding a New Analysis Pass
1. Create pass in `move-stackless-bytecode/src/`
2. Register in `function_target_pipeline.rs`
3. Add tests with expected bytecode output

### Modifying Boogie Generation
1. Edit translators in `move-prover-boogie-backend/src/boogie_backend/`
2. Update prelude templates in `prelude/` if needed
3. Update snapshots: `cargo insta test -p sui-prover`

## Important Notes

- **Never disable tests** - all tests must pass
- **Update snapshots** when changing Boogie output - don't leave `.snap.new` files
- **Timeout issues** - verification can be slow; use `--timeout` flag
- **Spec annotations** - only functions with `#[spec(prove)]` are verified
