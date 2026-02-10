---
name: sui-prover
description: Help with the Sui Prover for formal verification of Move smart contracts. Use when the user wants to verify Move code, debug verification failures, write specifications, or understand prover options.
argument-hint: [question, flags, or function name]
allowed-tools: Read, Grep, Glob, Bash
---

# Sui Prover

Help the user with the Sui Prover -- running verification, writing specifications, debugging failures, and understanding results. If arguments are provided, incorporate them. For the full specification API reference (math types, vector iterators, attributes), see [spec-reference.md](spec-reference.md).

## Installation

```bash
brew install asymptotic-code/sui-prover/sui-prover
```

### Move.toml Setup

The Sui Prover relies on implicit dependencies. Remove any direct dependencies to `Sui` and `MoveStdlib` from `Move.toml`:

```toml
# DELETE this line if present:
Sui = { git = "https://github.com/MystenLabs/sui.git", subdir = "crates/sui-framework/packages/sui-framework", rev = "framework/testnet", override = true }
```

If you need to reference Sui directly, put the specs in a separate package.

## Running the Prover

Run from the directory containing `Move.toml`:

```bash
sui-prover
sui-prover --path ./my_project
sui-prover --verbose --timeout 60
```

If the user provides arguments like `$ARGUMENTS`, pass them to `sui-prover` directly.

## Writing Specifications

To verify a function, write a specification function annotated with `#[spec(prove)]`. The spec has the same signature as the function under test and follows this structure:

```move
#[spec(prove)]
fun my_function_spec(args): ReturnType {
    // 1. Preconditions assumed on arguments
    requires(precondition);

    // 2. Capture old state if needed
    let old_state = clone!(mutable_ref);

    // 3. Call the function under test
    let result = my_function(args);

    // 4. Postconditions that must hold
    ensures(postcondition);

    // 5. Return the result
    result
}
```

### How Specs Compose

- **Naming convention**: A spec named `<function_name>_spec` is automatically used as an opaque summary when the prover verifies other functions that call `<function_name>`. The prover substitutes the spec's `requires`/`ensures` contract instead of inlining the function body.
- **`#[spec(prove)]`**: The spec is verified by the prover. Without `prove`, the spec is not checked itself, but is still used when proving other functions that depend on it.
- **`#[spec(prove, focus)]`**: Only verify this spec (and other focused specs). Useful for debugging. Do not commit `focus` — it skips all non-focused specs.
- **`no_opaque`**: By default, when proving `bar_spec`, the prover uses `foo_spec` (if it exists) as an opaque summary for `foo`. Adding `#[spec(prove, no_opaque)]` forces the prover to also include the actual implementation of called functions, not just their specs.
- **Scenario specs**: A spec without the `_spec` naming convention and without a `target` attribute is a standalone scenario — it's verified but not used as a summary for other proofs.

### Cross-Module Specs

Use `target` to spec a function in a different module:

```move
module 0x43::foo_spec {
    #[spec(prove, target = foo::inc)]
    public fun inc_spec(x: u64): u64 {
        let res = foo::inc(x);
        ensures(res == x + 1);
        res
    }
}
```

To access private members/functions from a cross-module spec, add `#[spec_only]` getter functions to the target module. These are only visible to the prover, not included in regular compilation.

### Specifying Abort Conditions

Specs must comprehensively describe when a function aborts. Use `asserts` for this:

```move
fun foo(x: u64, y: u64): u64 {
    assert!(x < y);
    x
}

#[spec(prove)]
fun foo_spec(x: u64, y: u64): u64 {
    asserts(x < y);  // foo aborts unless x < y
    let res = foo(x, y);
    res
}
```

For **overflow aborts**, cast to a wider type in the assertion:

```move
#[spec(prove)]
fun add_spec(x: u64, y: u64): u64 {
    asserts((x as u128) + (y as u128) <= u64::max_value!() as u128);
    let res = add(x, y);
    res
}
```

To **skip abort checking** entirely, use `ignore_abort`:

```move
#[spec(prove, ignore_abort)]
fun add_spec(x: u64, y: u64): u64 {
    let res = add(x, y);
    ensures(res == x + y);
    res
}
```

### Putting Specs in a Separate Package

Currently, specs may cause compile errors when placed alongside regular Move code due to prover-specific changes in the compilation pipeline. If this happens, create a separate package for specs and use the `target` attribute to reference functions in the original package.

### Example: Verifying an LP Withdraw

Consider a `withdraw` function for a liquidity pool:

```move
module amm::simple_lp;

use sui::balance::{Balance, Supply, zero};

public struct LP<phantom T> has drop {}

public struct Pool<phantom T> has store {
    balance: Balance<T>,
    shares: Supply<LP<T>>,
}

public fun withdraw<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    if (shares_in.value() == 0) {
        shares_in.destroy_zero();
        return zero()
    };

    let balance = pool.balance.value();
    let shares = pool.shares.supply_value();

    let balance_to_withdraw = (((shares_in.value() as u128) * (balance as u128))
        / (shares as u128)) as u64;

    pool.shares.decrease_supply(shares_in);
    pool.balance.split(balance_to_withdraw)
}
```

A specification proving that the share price does not decrease on withdrawal:

```move
#[spec_only]
use prover::prover::{requires, ensures};

#[spec(prove)]
fun withdraw_spec<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    requires(shares_in.value() <= pool.shares.supply_value());

    let old_pool = clone!(pool);

    let result = withdraw(pool, shares_in);

    let old_balance = old_pool.balance.value().to_int();
    let new_balance = pool.balance.value().to_int();
    let old_shares = old_pool.shares.supply_value().to_int();
    let new_shares = pool.shares.supply_value().to_int();

    // Share price does not decrease: new_balance/new_shares >= old_balance/old_shares
    ensures(new_shares.mul(old_balance).lte(old_shares.mul(new_balance)));

    result
}
```

Key points from this example:
- `requires(...)` specifies preconditions assumed on arguments
- `clone!(pool)` captures the state of a mutable reference before the call
- `.to_int()` converts to unbounded integers (spec-only) to avoid overflow in conditions
- `.mul()`, `.lte()` are spec-only operators on unbounded integers
- `ensures(...)` specifies postconditions that must hold after the call

### Core Specification Functions

Import with `use prover::prover::*`:

| Function | Description |
|----------|-------------|
| `requires(condition)` | Precondition assumed on arguments |
| `ensures(condition)` | Postcondition that must hold after the call |
| `asserts(condition)` | Assert condition is true, or function aborts |
| `clone!(ref)` | Capture a snapshot of a reference's value at this point |
| `implies(p, q)` | Logical implication (`!p \|\| q`) |
| `forall!<T>(\|x\| predicate(x))` | Universal quantification |
| `exists!<T>(\|x\| predicate(x))` | Existential quantification |
| `invariant!(\|\| { ... })` | Inline loop invariant (place before loop) |
| `.to_int()` | Convert primitive to unbounded integer (spec-only) |
| `.to_real()` | Convert primitive to arbitrary-precision real (spec-only) |
| `fresh<T>()` | Create an unconstrained value of type T |

### Common Patterns

**Pure functions** - Mark with `#[ext(pure)]` to use in specs:
```move
#[ext(pure)]
fun max(a: u64, b: u64): u64 { if (a >= b) { a } else { b } }
```

**Inline loop invariants** - Use `invariant!` before the loop:
```move
invariant!(|| {
    ensures(i <= n);
    ensures(sum == (i as u128) * ((i as u128) + 1) / 2);
});
while (i < n) {
    i = i + 1;
    sum = sum + (i as u128);
};
```

**External loop invariants** - Define as separate functions (alternative to inline):
```move
#[spec_only(loop_inv(target = sum_to_n_spec))]
#[ext(no_abort)]
fun sum_loop_inv(i: u64, n: u64, sum: u128): bool {
    i <= n && sum == (i as u128) * ((i as u128) + 1) / 2
}
```

**Targeting external functions**:
```move
#[spec(prove, target = 0x2::transfer::public_transfer)]
fun public_transfer_spec<T: key + store>(obj: T, recipient: address) { ... }
```

## Ghost Variables

Ghost variables are spec-only globals for propagating information between specifications. Import with `use prover::ghost::*`.

### Example: Verifying Event Emission

Building on the LP example, suppose `withdraw` emits an event on large withdrawals:

```move
const LARGE_WITHDRAW_AMOUNT: u64 = 10000;

public struct LargeWithdrawEvent has copy, drop {}

fun emit_large_withdraw_event() {
    event::emit(LargeWithdrawEvent { });
    requires(*global<LargeWithdrawEvent, bool>());
}
```

Use a ghost variable to verify the event is emitted correctly:

```move
#[spec_only]
use prover::ghost::{declare_global, global};

#[spec(prove)]
fun withdraw_spec<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    requires(shares_in.value() <= pool.shares.supply_value());

    declare_global<LargeWithdrawEvent, bool>();

    let old_pool = clone!(pool);
    let shares_in_value = shares_in.value();

    let result = withdraw(pool, shares_in);

    // ... share price postconditions ...

    if (shares_in_value >= LARGE_WITHDRAW_AMOUNT) {
        ensures(*global<LargeWithdrawEvent, bool>());
    };

    result
}
```

Key points:
- `declare_global<Key, Type>()` declares a ghost variable at the start of a spec
- The `Key` type is usually a user struct or a spec-only struct (e.g., `public struct MyGhostKey {}`)
- `global<Key, Type>()` reads the ghost variable's current value
- Ghost variables can be `requires`'d inside the functions that set them
- Use conditional `ensures` with regular `if` statements for conditional postconditions

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
```

### 4. Generate Only (Skip Z3)
```bash
sui-prover --generate-only --keep-temp
```

### 5. Split Verification Paths
```bash
sui-prover --split-paths 4
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
| Loop verification fails | Add/strengthen loop invariant (`invariant!` or external) |
| Pure function not usable in spec | Add `#[ext(pure)]` attribute |
| Abort condition verification fails | Add `asserts()` for all abort paths, or use `ignore_abort` |
| Spec uses wrong function body | Check `no_opaque` — by default specs are used as opaque summaries |
| Compile errors adding specs | Put specs in a separate package, use `target` attribute |

## Prerequisites

The prover requires **Z3** (SMT solver) and **Boogie** (verification condition generator) to be installed.
