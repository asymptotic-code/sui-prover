# Running the Sui Prover

This guide covers how to run the Sui Prover for formal verification of Move smart contracts.

## Quick Start

```bash
# Run from directory containing Move.toml
sui-prover

# Specify package path
sui-prover --path ./my_project

# Common workflow
sui-prover --verbose --timeout 60
```

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

### Basic Structure

Specifications are written as functions marked with `#[spec(prove)]`:

```move
module 0x42::example {
    use prover::prover::{requires, ensures, asserts};

    fun add(x: u64, y: u64): u64 {
        x + y
    }

    #[spec(prove)]
    fun add_spec(x: u64, y: u64): u64 {
        // Precondition: sum must not overflow
        asserts((x as u128) + (y as u128) <= (u64::max_value!() as u128));

        // Call the function under test
        let result = add(x, y);

        // Postconditions
        ensures(result == x + y);
        ensures(result >= x);
        ensures(result >= y);

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

### Vector Iterator Functions

Import with `use prover::vector_iter::*`:

| Function | Description |
|----------|-------------|
| `all!<T>(&vec, \|x\| pred(x))` | All elements satisfy predicate |
| `any!<T>(&vec, \|x\| pred(x))` | Any element satisfies predicate |
| `count!<T>(&vec, \|x\| pred(x))` | Count elements satisfying predicate |
| `map!<T, U>(&vec, \|x\| f(x))` | Transform vector elements |
| `filter!<T>(&vec, \|x\| pred(x))` | Filter vector elements |
| `find!<T>(&vec, \|x\| pred(x))` | Find first matching element |
| `find_index!<T>(&vec, \|x\| pred(x))` | Find index of first match |
| `find_indices!<T>(&vec, \|x\| pred(x))` | Find all matching indices |
| `sum!<T>(&vec)` | Sum vector elements |
| `sum_map!<T, U>(&vec, \|x\| f(x))` | Sum mapped elements |

All functions have `_range!` variants: `all_range!(&vec, start, end, |x| ...)`.

### Ghost Variables

Import with `use prover::ghost::*`:

```move
#[spec(prove)]
fun ghost_example_spec() {
    // Declare a ghost variable
    ghost::declare_global_mut<MyKey, u64>();

    // Get mutable reference and modify
    let ghost_ref = ghost::borrow_mut<MyKey, u64>();
    *ghost_ref = 42;

    // Read current value
    ensures(ghost::global<MyKey, u64>() == 42);
}
```

### Mathematical Types (Spec-Only)

The prover provides arbitrary-precision mathematical types for specifications.

#### `std::integer::Integer`

Arbitrary-precision integers for specifications. Convert from primitives using `.to_int()`:

```move
use std::integer::Integer;

#[spec(prove)]
fun integer_example_spec() {
    let a: Integer = 42u64.to_int();
    let b: Integer = 10u64.to_int();

    // Arithmetic
    ensures(a.add(b) == 52u64.to_int());
    ensures(a.sub(b) == 32u64.to_int());
    ensures(a.mul(b) == 420u64.to_int());
    ensures(a.div(b) == 4u64.to_int());
    ensures(a.mod(b) == 2u64.to_int());

    // Comparison
    ensures(a.gt(b));
    ensures(b.lt(a));
    ensures(a.gte(42u64.to_int()));
    ensures(b.lte(10u64.to_int()));

    // Math functions
    ensures(16u64.to_int().sqrt() == 4u64.to_int());
    ensures(2u64.to_int().pow(10u64.to_int()) == 1024u64.to_int());
    ensures(5u64.to_int().neg().abs() == 5u64.to_int());
}
```

**Integer methods:**
| Method | Description |
|--------|-------------|
| `add`, `sub`, `mul`, `div`, `mod` | Arithmetic operations |
| `neg`, `abs` | Negation, absolute value |
| `sqrt`, `pow` | Square root, exponentiation |
| `lt`, `gt`, `lte`, `gte` | Comparisons (return `bool`) |
| `bit_or`, `bit_and`, `bit_xor`, `bit_not` | Bitwise operations |
| `shl`, `shr` | Shift left/right |
| `is_pos`, `is_neg` | Sign checks |
| `to_u8`, `to_u64`, etc. | Convert back to primitive |
| `to_real` | Convert to Real |

**Conversion methods on primitives:**
- `42u64.to_int()` - unsigned interpretation
- `42u64.to_signed_int()` - signed interpretation (for two's complement)

#### `std::real::Real`

Arbitrary-precision real numbers for specifications. Convert using `.to_real()`:

```move
use std::real::Real;

#[spec(prove)]
fun real_example_spec() {
    let x: Real = 16u64.to_real();

    // Arithmetic
    ensures(x.sqrt() == 4u64.to_real());
    ensures(x.div(4u64.to_real()) == 4u64.to_real());

    // Exponentiation (integer exponent)
    ensures(2u64.to_real().exp(3u64.to_int()) == 8u64.to_real());

    // Comparison
    ensures(x.gt(10u64.to_real()));
}
```

**Real methods:**
| Method | Description |
|--------|-------------|
| `add`, `sub`, `mul`, `div` | Arithmetic operations |
| `neg` | Negation |
| `sqrt` | Square root |
| `exp` | Exponentiation (takes Integer exponent) |
| `lt`, `gt`, `lte`, `gte` | Comparisons (return `bool`) |
| `to_integer` | Convert to Integer (truncates) |
| `to_u8`, `to_u64`, etc. | Convert to primitive (via Integer) |

#### `std::q32::Q32`, `std::q64::Q64`, `std::q128::Q128`

Signed fixed-point types with 32, 64, or 128 fractional bits respectively. Useful for precise decimal arithmetic in specifications.

```move
use std::q64::Q64;

#[spec(prove)]
fun fixed_point_example_spec(a: u64, b: u64) {
    requires(b > 0);

    // Convert to fixed-point
    let x: Q64 = a.to_q64();
    let y: Q64 = b.to_q64();

    // Create from quotient (a / b as fixed-point)
    let ratio: Q64 = Q64::quot(a.to_int(), b.to_int());

    // Arithmetic preserves relationships
    let product = ratio.mul(y);
    ensures(product.floor().lte(a.to_int()));

    // Comparison
    ensures(x.div(y).lte(ratio.add(1u64.to_q64())));

    // Rounding
    ensures(ratio.floor().lte(ratio.ceil()));
    ensures(ratio.is_int() ==> ratio.floor() == ratio.ceil());
}
```

**Fixed-point methods:**
| Method | Description |
|--------|-------------|
| `quot(num, den)` | Create from fraction num/den |
| `add`, `sub`, `mul`, `div` | Arithmetic operations |
| `neg`, `abs` | Negation, absolute value |
| `sqrt`, `pow` | Square root, exponentiation |
| `lt`, `gt`, `lte`, `gte` | Comparisons (return `bool`) |
| `floor`, `ceil`, `round` | Rounding to Integer |
| `to_int`, `to_real` | Convert to Integer or Real |
| `is_pos`, `is_neg`, `is_int` | Predicates |
| `raw` | Access raw Integer representation (value * 2^bits) |

**Conversions to fixed-point:**
- `42u64.to_q32()` / `.to_q64()` / `.to_q128()` - from primitive
- `my_integer.to_q64()` - from Integer
- `my_real.to_q64()` - from Real
- `my_uq64_64.to_q64()` - from `UQ64_64`
- `my_uq32_32.to_q32()` - from `UQ32_32`
- `my_fp32.to_q32()` - from `FixedPoint32`

## Attributes Reference

### `#[spec(...)]` - Specification Functions

Marks a function as a specification to verify.

| Parameter | Description |
|-----------|-------------|
| `prove` | Verify this specification |
| `skip` | Skip verification |
| `focus` | Mark as focused (verify only focused specs) |
| `target = <PATH>` | Target external function (e.g., `target = 0x42::module::func`) |
| `include = <PATH>` | Include another spec's behavior |
| `ignore_abort` | Don't check abort conditions |
| `no_opaque` | Inline called functions instead of using their specs |
| `uninterpreted = <NAME>` | Treat pure function as uninterpreted |
| `extra_bpl = b"<file>"` | Load extra Boogie code |
| `boogie_opt = b"<opt>"` | Pass custom Boogie options |

Examples:
```move
#[spec(prove)]
#[spec(prove, target = 0x42::foo::bar)]
#[spec(prove, ignore_abort)]
#[spec(prove, no_opaque)]
#[spec(prove, target = 0x42::foo::bar, include = 0x42::specs::helper_spec)]
```

### `#[ext(...)]` - Function Characteristics

Marks functions with special characteristics.

| Parameter | Description |
|-----------|-------------|
| `pure` | Function is pure (deterministic, no side effects); usable in specs |
| `no_abort` | Function never aborts |
| `axiom` | Function is defined axiomatically |

Examples:
```move
#[ext(pure)]
fun max(a: u64, b: u64): u64 { if (a >= b) a else b }

#[ext(no_abort)]
fun safe_get(v: &vector<u64>, i: u64): u64 { ... }

#[ext(axiom)]
fun sqrt(x: u64): u64;  // No body, assumed correct
```

### `#[spec_only(...)]` - Specification-Only Items

Marks items that exist only for specification purposes.

| Parameter | Description |
|-----------|-------------|
| (none) | Basic spec-only item |
| `(axiom)` | Axiom definition |
| `(inv_target = <TYPE>)` | Datatype invariant for specified type |
| `(loop_inv(target = <FUNC>))` | External loop invariant |
| `(loop_inv(target = <FUNC>, label = N))` | Loop invariant with label |
| `(include = <PATH>)` | Include spec module |
| `(extra_bpl = b"<file>")` | Load extra Boogie code |

Examples:
```move
#[spec_only]
fun helper_predicate(x: u64): bool { x > 0 }

#[spec_only(axiom)]
fun sqrt_axiom(x: u64): u64 { ... }

#[spec_only(inv_target = MyStruct)]
public fun MyStruct_inv(self: &MyStruct): bool {
    self.value > 0
}

#[spec_only(loop_inv(target = my_func_spec))]
fun loop_inv_for_my_func() { }
```

## Common Patterns

### Loop Invariants (External)

Loop invariants are defined as separate functions marked with `#[spec_only(loop_inv(target = ...))]`.
The invariant function returns a boolean conjunction of all invariant conditions.

```move
// External loop invariant - returns conjunction of conditions
#[spec_only(loop_inv(target = sum_to_n_spec))]
#[ext(no_abort)]
fun sum_loop_inv(i: u64, n: u64, sum: u128): bool {
    i <= n && sum == (i as u128) * ((i as u128) + 1) / 2
}

// The spec function containing the loop
#[spec(prove)]
fun sum_to_n_spec(n: u64): u128 {
    let mut sum: u128 = 0;
    let mut i: u64 = 0;

    while (i < n) {
        i = i + 1;
        sum = sum + (i as u128);
    };

    ensures(sum == (n as u128) * ((n as u128) + 1) / 2);
    sum
}
```

**Key points:**
- The invariant function parameters must match the loop variables
- Return a `bool` with conditions joined by `&&`
- Add `#[ext(no_abort)]` or `#[ext(pure)]` attribute
- For cloned values, use `__old_` prefix in parameter names (e.g., `__old_n` for `clone!(&n)`)
- For multiple loops in one function, use `label = N` (0-indexed):

```move
#[spec_only(loop_inv(target = my_spec, label = 0))]
#[ext(no_abort)]
fun first_loop_inv(...): bool { ... }

#[spec_only(loop_inv(target = my_spec, label = 1))]
#[ext(no_abort)]
fun second_loop_inv(...): bool { ... }
```

### Pure Functions

```move
#[ext(pure)]
fun max(a: u64, b: u64): u64 {
    if (a >= b) { a } else { b }
}

#[spec(prove)]
fun max_spec(a: u64, b: u64): u64 {
    let result = max(a, b);
    ensures(result >= a);
    ensures(result >= b);
    ensures(result == a || result == b);
    result
}
```

### Quantifiers

```move
#[ext(pure)]
fun is_positive(x: &u64): bool { *x > 0 }

#[spec(prove)]
fun quantifier_example_spec() {
    // All u64 values are >= 0 (trivially true)
    ensures(forall!<u64>(|x| x >= 0));

    // There exists a u64 equal to 42
    ensures(exists!<u64>(|x| x == 42));
}
```

### Vector Specifications

```move
#[ext(pure)]
fn is_even(x: &u64): bool { *x % 2 == 0 }

#[spec(prove)]
fun vector_spec() {
    let v = vector[2, 4, 6, 8];

    ensures(all!<u64>(&v, |x| is_even(x)));
    ensures(count!<u64>(&v, |x| *x > 5) == 2);
    ensures(sum!<u64>(&v) == 20u64.to_int());
}
```

### Capturing Old Values with clone!

```move
#[spec(prove)]
fun increment_spec(x: &mut u64) {
    let old_x = clone!(x);
    increment(x);
    ensures(*x == *old_x + 1);
}
```

### Datatype Invariants

```move
public struct PositiveNumber {
    value: u64
}

#[spec_only(inv_target = PositiveNumber)]
public fun PositiveNumber_inv(self: &PositiveNumber): bool {
    self.value > 0
}

// The invariant is automatically checked on construction and modification
#[spec(prove)]
fun create_positive_spec(): PositiveNumber {
    let result = create_positive(42);
    ensures(result.value == 42);
    result
}
```

### Targeting External Functions

```move
// Verify a function from another module
#[spec(prove, target = 0x2::transfer::public_transfer)]
fun public_transfer_spec<T: key + store>(obj: T, recipient: address) {
    requires(/* preconditions */);
    public_transfer(obj, recipient);
    ensures(/* postconditions */);
}
```

## Debugging Verification Failures

### 1. Enable Verbose Output
```bash
sui-prover --verbose
```

### 2. Keep Temporary Files
```bash
sui-prover --keep-temp
# Inspect generated .bpl files in the output
```

### 3. Dump Bytecode
```bash
sui-prover --dump-bytecode
# Examine the bytecode transformations
```

### 4. Generate Only (No Verification)
```bash
sui-prover --generate-only --keep-temp
# Review Boogie code without running Z3
```

### 5. Filter to Specific Functions
```bash
sui-prover --functions my_failing_spec
```

### 6. Split Verification Paths
```bash
sui-prover --split-paths 4
# Helps isolate which execution path fails
```

### 7. Increase Timeout
```bash
sui-prover --timeout 120
```

## Interpreting Results

### Success
```
Verification successful for module::function_spec
```

### Failure with Counterexample
The prover shows:
- Which assertion failed
- Variable values that cause the failure
- Execution trace leading to the failure

Use `--no-counterexample-trace` to hide the trace if it's too verbose.

### Timeout
Indicates the solver couldn't prove or disprove within the time limit. Try:
- Increasing `--timeout`
- Simplifying the specification
- Using `--split-paths`
- Adding intermediate assertions

## Prerequisites

The prover requires these external tools to be installed:
- **Z3** - SMT solver
- **Boogie** - Verification condition generator

## Common Issues

| Issue | Solution |
|-------|----------|
| Timeout on complex specs | Increase `--timeout`, use `--split-paths`, simplify spec |
| "Function not found" | Check module path in `target = ...` attribute |
| Counterexample unclear | Use `--verbose`, add intermediate `ensures()` |
| Loop verification fails | Add/strengthen external loop invariant |
| Pure function not usable in spec | Add `#[ext(pure)]` attribute |
