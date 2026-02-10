---
name: sui-prover
description: Help with the Sui Prover for formal verification of Move smart contracts. Use when the user wants to verify Move code, debug verification failures, write specifications, or understand prover options.
argument-hint: [question, flags, or function name]
allowed-tools: Read, Grep, Glob, Bash
---

# Sui Prover

Help the user with the Sui Prover -- running verification, writing specifications, debugging failures, and understanding results. If arguments are provided, incorporate them. For detailed specification syntax, see [spec-reference.md](spec-reference.md).

## Quick Start

Run from the directory containing `Move.toml`:

```bash
sui-prover
sui-prover --path ./my_project
sui-prover --verbose --timeout 60
```

If the user provides arguments like `$ARGUMENTS`, pass them to `sui-prover` directly.

## CLI Options

### General Options

| Flag | Description |
|------|-------------|
| `--timeout, -t <SECONDS>` | Verification timeout (default: 45) |
| `--verbose, -v` | Display detailed verification progress |
| `--keep-temp, -k` | Keep temporary .bpl files after verification |
| `--generate-only, -g` | Generate Boogie code without running verifier |
| `--dump-bytecode, -d` | Dump bytecode to file for debugging |
| `--no-counterexample-trace` | Don't display counterexample trace on failure |
| `--explain` | Explain verification outputs via LLM |
| `--ci` | Enable CI mode for continuous integration |

### Filtering Options

| Flag | Description |
|------|-------------|
| `--modules <NAMES>` | Verify only specified modules |
| `--functions <NAMES>` | Verify only specified functions |

### Advanced Options

| Flag | Description |
|------|-------------|
| `--skip-spec-no-abort` | Skip checking spec functions that do not abort |
| `--skip-fun-no-abort` | Skip checking `#[ext(no_abort)]` or `#[ext(pure)]` functions |
| `--split-paths <N>` | Split verification into separate proof goals per execution path |
| `--boogie-file-mode, -m <MODE>` | Boogie running mode: `function` (default) or `module` |
| `--use-array-theory` | Use array theory in Boogie encoding |
| `--no-bv-int-encoding` | Encode integers as bitvectors instead of mathematical integers |
| `--stats` | Dump control-flow graphs and function statistics |
| `--force-timeout` | Force kill boogie process if timeout is exceeded |

### Package Options

| Flag | Description |
|------|-------------|
| `--path, -p <PATH>` | Path to package directory with Move.toml |
| `--install-dir <PATH>` | Installation directory for compiled artifacts |
| `--force` | Force recompilation of all packages |
| `--skip-fetch-latest-git-deps` | Skip fetching latest git dependencies |

### Remote/Cloud Options

| Flag | Description |
|------|-------------|
| `--cloud` | Use cloud configuration for remote verification |
| `--cloud-config-path <PATH>` | Path to cloud config (default: `$HOME/.asymptotic/sui_prover.toml`) |
| `--cloud-config` | Create/update cloud configuration interactively |

## Writing Specifications

Specifications are functions marked with `#[spec(prove)]`:

```move
module 0x42::example {
    use prover::prover::{requires, ensures, asserts};

    fun add(x: u64, y: u64): u64 {
        x + y
    }

    #[spec(prove)]
    fun add_spec(x: u64, y: u64): u64 {
        asserts((x as u128) + (y as u128) <= (u64::max_value!() as u128));
        let result = add(x, y);
        ensures(result == x + y);
        ensures(result >= x);
        result
    }
}
```

### Core Specification Functions

Import with `use prover::prover::*`:

| Function | Description |
|----------|-------------|
| `requires(condition)` | Precondition that must hold before execution |
| `ensures(condition)` | Postcondition that must hold after execution |
| `asserts(condition)` | Assert condition is true, or function aborts |
| `clone!(&var)` | Capture variable's value at this point for later comparison |
| `forall!<T>(\|x\| predicate(x))` | Universal quantification |
| `exists!<T>(\|x\| predicate(x))` | Existential quantification |
| `fresh()` | Uninterpreted function placeholder |

### Common Patterns

**Pure functions** - Mark with `#[ext(pure)]` to use in specs:
```move
#[ext(pure)]
fun max(a: u64, b: u64): u64 { if (a >= b) { a } else { b } }
```

**Loop invariants** - Define as separate functions:
```move
#[spec_only(loop_inv(target = sum_to_n_spec))]
#[ext(no_abort)]
fun sum_loop_inv(i: u64, n: u64, sum: u128): bool {
    i <= n && sum == (i as u128) * ((i as u128) + 1) / 2
}
```

**Capturing old values**:
```move
let old_x = clone!(x);
increment(x);
ensures(*x == *old_x + 1);
```

**Targeting external functions**:
```move
#[spec(prove, target = 0x2::transfer::public_transfer)]
fun public_transfer_spec<T: key + store>(obj: T, recipient: address) { ... }
```

For the full specification reference (math types, vector iterators, ghost variables, attributes), see [spec-reference.md](spec-reference.md).

## Debugging Verification Failures

When verification fails, follow these steps in order:

### 1. Enable Verbose Output
```bash
sui-prover --verbose
```

### 2. Filter to the Failing Function
```bash
sui-prover --functions my_failing_spec
```

### 3. Keep and Inspect Temporary Files
```bash
sui-prover --keep-temp
# Inspect the generated .bpl Boogie files
```

### 4. Generate Only (Skip Z3)
```bash
sui-prover --generate-only --keep-temp
# Review Boogie code without running Z3
```

### 5. Split Verification Paths
```bash
sui-prover --split-paths 4
# Isolate which execution path fails
```

### 6. Increase Timeout
```bash
sui-prover --timeout 120
```

## Interpreting Results

**Success**: `Verification successful for module::function_spec`

**Failure with counterexample**: Shows which assertion failed, variable values causing failure, and execution trace. Use `--no-counterexample-trace` to hide verbose traces.

**Timeout**: Solver couldn't prove or disprove within the time limit. Try:
- Increasing `--timeout`
- Simplifying the specification
- Using `--split-paths`
- Adding intermediate assertions

## Common Issues

| Issue | Solution |
|-------|----------|
| Timeout on complex specs | Increase `--timeout`, use `--split-paths`, simplify spec |
| "Function not found" | Check module path in `target = ...` attribute |
| Counterexample unclear | Use `--verbose`, add intermediate `ensures()` |
| Loop verification fails | Add/strengthen external loop invariant |
| Pure function not usable in spec | Add `#[ext(pure)]` attribute |

## Prerequisites

The prover requires **Z3** (SMT solver) and **Boogie** (verification condition generator) to be installed.
