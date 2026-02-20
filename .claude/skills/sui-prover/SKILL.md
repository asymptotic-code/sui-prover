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

### Common Abort Patterns

**Overflow/underflow** - Use `.to_int()` for arbitrary-precision arithmetic in asserts:
```move
// For: a + b
asserts(a.to_int().add(b.to_int()).lte(std::u64::max_value!().to_int()));

// For: a * b / c
let result = a.to_int().mul(b.to_int()).div(c.to_int());
asserts(result.lte(std::u64::max_value!().to_int()));
```

**Table/dynamic field access** - Assert existence before borrow:
```move
asserts(table.contains(key));
let value = table.borrow(key);
```
Exception: if the implementation guards with `if (!table.contains(key)) { return }`, no assert is needed since the code won't abort.

**Division** - Assert non-zero divisor:
```move
asserts(divisor != 0);
```

**`bag::contains_with_type` pattern** - `bag::contains<K>` does NOT connect with `bag::borrow<K, V>` in the prover, but `bag::contains_with_type<K, V>` does:
```move
// WRONG - prover can't connect contains with borrow
asserts(bag::contains(&bag, key));
let value = bag::borrow<K, V>(&bag, key); // prover thinks this could abort

// CORRECT - prover connects contains_with_type with borrow
asserts(bag::contains_with_type<K, V>(&bag, key));
let value = bag::borrow<K, V>(&bag, key); // prover knows this won't abort
```

### Common Mistakes

**Asserts must come before the function call that could abort:**
```move
// WRONG: Assert after function call that could abort
let result = risky_function(a, b);
asserts(a != 0);  // Too late - function already aborted

// CORRECT: Assert before function call
asserts(a != 0);
let result = risky_function(a, b);
```

**Reuse asserts from proven specs.** When your function calls another function that already has a proven spec, copy all asserts from that spec:
```move
// If pow_spec has: asserts(base.to_int().pow(exp.to_int()).lte(max.to_int()));
// Then in your spec that internally calls pow():
fun my_function_spec(a: u64, b: u8): u64 {
    asserts(a.to_int().pow(b.to_int()).lte(std::u64::max_value!().to_int()));
    let result = my_module::my_function(a, b);
    result
}
```

**Early return guards** - When implementation has `if (x == y) { return }`, asserts for code after the early return must be guarded in the spec:
```move
if (x != y) {
    asserts(/* conditions for code after early return */);
};
```

### Common Patterns

**Pure functions** - Mark with `#[ext(pure)]` to use in specs. Add to all pure getter/view functions — field accessors, view functions, etc. When a getter calls another module's function, that function also needs `#[ext(pure)]`:
```move
#[ext(pure)]
fun max(a: u64, b: u64): u64 { if (a >= b) { a } else { b } }
```

**Private struct field access** - Use `#[test_only]` accessor functions in the implementation:
```move
// In implementation module:
#[test_only]
public fun get_field_name(s: &MyStruct): String { s.name }

// In spec:
ensures(module::get_field_name(&result) == expected);
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

**`no_opaque` for same-file public functions** - If functions `x` and `y` are both public, both have specs in one file, and `y` is called inside `x`, then `y`'s spec should have `no_opaque` so the prover uses the implementation (not `y_spec`) when proving `x_spec`. Exception: if `y` has a loop with `requires(forall!(...))`, keep it opaque to avoid timeouts.

**`boogie_opt` for complex specs** - For specs with many calculations, add `boogie_opt=b"vcsSplitOnEveryAssert"` to improve performance:
```move
#[spec(prove, target=module::complex_func, boogie_opt=b"vcsSplitOnEveryAssert")]
```

**Prefer `asserts` over `requires`** where possible. Use `requires` only for preconditions that truly constrain inputs.

**Ensures with table access** - When ensures use getters that internally call `table.borrow`, add a contains check first:
```move
module::set_value(storage, key, value);
ensures(module::contains(storage, key));       // MUST come first
ensures(module::get_value(storage, key) == value);
```

**Extra BPL prelude files** - When the prover fails with `use of undeclared function: $X_module_native_func$pure`, create a `.bpl` prelude file with the missing function definition:
```move
#[spec_only(extra_bpl = b"mymodule_prelude.bpl")]
module specs::mymodule;
```
Place the BPL file in the same directory as the spec module.

**Targeting external functions**:
```move
#[spec(prove, target = 0x2::transfer::public_transfer)]
fun public_transfer_spec<T: key + store>(obj: T, recipient: address) { ... }
```

**Ghost variables for `transfer::public_transfer`** - When a spec involves `transfer::public_transfer` (directly or indirectly), declare ghost variables:
```move
#[spec_only]
use specs::transfer_spec::{SpecTransferAddress, SpecTransferAddressExists};

#[spec(prove, target = module::func_that_transfers)]
fun func_spec<T>(...) {
    ghost::declare_global_mut<SpecTransferAddress, address>();
    ghost::declare_global_mut<SpecTransferAddressExists, bool>();
    // ... rest of spec
    ensures(*ghost::global<SpecTransferAddressExists, bool>());
    ensures(*ghost::global<SpecTransferAddress, address>() == recipient);
}
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

### 1. Interpret the Error

**"Code aborts"** → Missing asserts. Add asserts to cover all abort paths in the function and nested calls. Trace through every function call and identify what can abort (overflow, table access, division by zero, assert! statements).

**"Assert does not hold"** → The assert condition is wrong. The condition should describe the precondition under which the code does not abort, but the current condition doesn't match reality. Recheck the logic.

### 2. Use Focus for Iterative Development
```move
#[spec(prove, focus, target = module::func)]  // Only verify this spec
```
Always use `focus` when developing a spec. Full suite takes very long.

### 3. Debugging Workflow
1. Add `focus` attribute to the spec you're working on
2. Run `sui-prover`
3. If "Code aborts": add missing asserts for abort conditions
4. If "Assert does not hold": fix the assert condition
5. Once passing with `focus`, remove `focus` and verify full suite

### 4. CLI Debugging Flags
```bash
sui-prover --verbose                    # Detailed output
sui-prover --functions my_failing_spec  # Filter to one function
sui-prover --keep-temp                  # Inspect generated .bpl files
sui-prover --generate-only --keep-temp  # Generate Boogie without running Z3
sui-prover --split-paths 4              # Split verification paths
sui-prover --timeout 120                # Increase timeout
```

## Interpreting Results

**Success**: `Verification successful for module::function_spec`

**Failure with counterexample**: Shows which assertion failed, variable values causing failure, and execution trace. Use `--no-counterexample-trace` to hide verbose traces.

**Timeout**: Solver couldn't prove or disprove within the time limit. Try:
- Increasing `--timeout`
- Simplifying the specification
- Using `--split-paths`
- Adding `boogie_opt=b"vcsSplitOnEveryAssert"` to the spec
- Adding intermediate assertions
- Nested table access in ensures is a common timeout cause — consider dropping ensures and keeping abort coverage only

## Common Issues

| Issue | Solution |
|-------|----------|
| "Code aborts" | Missing asserts — add asserts for all abort paths in target and nested calls |
| "Assert does not hold" | Assert condition is wrong — recheck the logic |
| Timeout on complex specs | Add `boogie_opt=b"vcsSplitOnEveryAssert"`, increase `--timeout`, use `--split-paths` |
| Timeout from nested table ensures | Drop ensures, keep abort coverage only (asserts without ensures) |
| "Function not found" | Check module path in `target = ...` attribute |
| Counterexample unclear | Use `--verbose`, add intermediate `ensures()` |
| Loop verification fails | Add/strengthen loop invariant (`invariant!` or external) |
| Pure function not usable in spec | Add `#[ext(pure)]` attribute; called functions also need it |
| Abort condition verification fails | Add `asserts()` for all abort paths, or use `ignore_abort` |
| Spec uses wrong function body | Check `no_opaque` — by default specs are used as opaque summaries |
| `bag::contains` not connecting with `borrow` | Use `bag::contains_with_type<K, V>` instead of `bag::contains<K>` |
| `undeclared function: $X_native$pure` | Create `.bpl` prelude file with the missing function, use `extra_bpl` |
| `undeclared global variable` for transfers | Declare ghost variables for `SpecTransferAddress`/`SpecTransferAddressExists` |
| `UID object type not found` | Known bug — skip spec for functions that destructure structs to extract UID |
| Compile errors adding specs | Put specs in a separate package, use `target` attribute |

## Known Issues

### UID Tracking Bug After Struct Destructuring
When a function destructures a struct to extract a UID and then calls `dynamic_field::remove` on that local UID, the prover loses type information and fails with:
```
error[E0022]: UID object type not found: 5
```
**Workaround:** Do not write a spec for such functions. The `skip` attribute does NOT help because the error occurs during bytecode transformation before specs are evaluated.

### Method Syntax Limitations
Method syntax works only when the function is defined in the same module as the receiver type:
- `bag::contains(bag, key)` → `bag.contains(key)` works (Bag defined in sui::bag)
- `dynamic_field::borrow(uid, key)` → cannot use method syntax (UID in sui::object, function in sui::dynamic_field)

## Prerequisites

The prover requires **Z3** (SMT solver) and **Boogie** (verification condition generator) to be installed.
