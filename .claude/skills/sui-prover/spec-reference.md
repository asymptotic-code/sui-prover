# Specification Reference

Detailed reference for Move specification syntax used with the Sui Prover.

## Package Layout

Place specification modules in a sibling `specs/` Move package next to the implementation `project/` package. Make the spec package depend on the implementation package and use `target` to specify implementation functions. When specifications need private implementation state, expose it through `#[test_only]` accessor functions in the implementation module and call the accessors with method syntax.

## Vector Iterator Functions

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
| `sum<T>(&vec)` | Sum vector elements (returns `Integer`) |
| `sum_map!<T, U>(&vec, \|x\| f(x))` | Sum mapped elements |

All macros have `_range!` variants: `all_range!(&vec, start, end, |x| ...)`. The `sum` and `sum_range` functions are called without `!` (they are native functions, not macros).

Example:
```move
#[spec(prove)]
fun vector_spec() {
    let v = vector[2, 4, 6, 8];
    ensures(all!<u64>(&v, |x| is_even(x)));
    ensures(count!<u64>(&v, |x| *x > 5) == 2);
    ensures(sum(&v) == 20u64.to_int());
}
```

## Ghost Variables

Ghost variables are spec-only globals for propagating information between specifications. Import with `use prover::ghost::*`.

Ghost variables are declared with two type-level arguments: a key type and a value type. The key is usually a user struct or a spec-only struct:

```move
#[mode(spec)]
public struct MyGhostKey {}
```

### Declaring and Reading

```move
#[mode(spec)]
use prover::ghost::{declare_global, global};

#[spec(prove)]
fun ghost_example_spec() {
    // Declare a ghost variable keyed by type pair
    declare_global<MyKey, bool>();

    // Read its value
    ensures(*global<MyKey, bool>());
}
```

### Mutable Ghost Variables

```move
#[mode(spec)]
use prover::ghost::{declare_global_mut, borrow_mut, global};

#[spec(prove)]
fun ghost_mut_example_spec() {
    declare_global_mut<MyKey, u64>();
    let ghost_ref = borrow_mut<MyKey, u64>();
    *ghost_ref = 42;
    ensures(*global<MyKey, u64>() == 42);
}
```

## Mathematical Types (Spec-Only)

### `std::integer::Integer`

Arbitrary-precision integers. Convert from primitives using `.to_int()`:

```move
use std::integer::Integer;

#[spec(prove)]
fun integer_example_spec() {
    let a: Integer = 42u64.to_int();
    let b: Integer = 10u64.to_int();
    ensures(a.add(b) == 52u64.to_int());
    ensures(a.sub(b) == 32u64.to_int());
    ensures(a.mul(b) == 420u64.to_int());
}
```

**Methods:**
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

**Conversions:**
- `42u64.to_int()` - unsigned interpretation
- `42u64.to_signed_int()` - signed interpretation (for two's complement)

### `std::real::Real`

Arbitrary-precision real numbers. Convert using `.to_real()`:

```move
use std::real::Real;

#[spec(prove)]
fun real_example_spec() {
    let x: Real = 16u64.to_real();
    ensures(x.sqrt() == 4u64.to_real());
    ensures(2u64.to_real().exp(3u64.to_int()) == 8u64.to_real());
}
```

**Methods:**
| Method | Description |
|--------|-------------|
| `add`, `sub`, `mul`, `div` | Arithmetic operations |
| `neg` | Negation |
| `sqrt` | Square root |
| `exp` | Exponentiation (takes Integer exponent) |
| `lt`, `gt`, `lte`, `gte` | Comparisons (return `bool`) |
| `to_integer` | Convert to Integer (truncates) |
| `to_u8`, `to_u64`, etc. | Convert to primitive (via Integer) |

### Fixed-Point Types: `Q32`, `Q64`, `Q128`

Signed fixed-point types with 32, 64, or 128 fractional bits. Import from `std::q32`, `std::q64`, `std::q128`.

```move
use std::q64::Q64;

#[spec(prove)]
fun fixed_point_example_spec(a: u64, b: u64) {
    requires(b > 0);
    let ratio: Q64 = Q64::quot(a.to_int(), b.to_int());
    ensures(ratio.floor().lte(a.to_int()));
}
```

**Methods:**
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

Marks a function as a specification.

**External target**: Every spec for an implementation function must use `target = <implementation-path>` because the spec lives in a sibling package.

**Without `prove`**: The spec is not verified itself, but is used when proving other functions that depend on it.

**With `prove`**: The spec is verified by the prover.

**Scenario specs**: A spec without a `target` attribute is a standalone scenario — verified but not associated with an implementation function.

| Parameter | Description |
|-----------|-------------|
| `prove` | Verify this specification |
| `skip` | Skip verification |
| `focus` | Mark as focused (verify only focused specs). Can be used on multiple specs simultaneously. |
| `target = <PATH>` | Target external function (e.g., `target = 0x42::module::func`) |
| `include = <PATH>` | Include another spec's behavior |
| `ignore_abort` | Don't check abort conditions. Allows omitting `asserts` for aborts. |
| `no_opaque` | Include actual implementations of called functions instead of using their targeted specs as opaque summaries. |
| `uninterpreted = <NAME>` | Treat pure function as uninterpreted |
| `extra_bpl = b"<file>"` | Load extra Boogie code |
| `boogie_opt = b"<opt>"` | Pass custom Boogie options |

Examples:
```move
#[spec(prove, target = 0x42::foo::bar)]
#[spec(prove, focus, target = 0x42::foo::bar)]
#[spec(prove, ignore_abort, target = 0x42::foo::bar)]
#[spec(prove, no_opaque, target = 0x42::foo::bar)]
#[spec(prove, target = 0x42::foo::bar, include = 0x42::specs::helper_spec)]
```

### `#[ext(...)]` - Function Characteristics

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

### `#[test_only]` - Implementation Getters

Use `#[test_only]` for getter or accessor functions added to implementation modules. The prover can call test-only getters without including them in production builds:

```move
#[test_only]
public fun get_field_name(self: &MyStruct): u64 {
    self.field_name
}
```

### `#[mode(spec), ext(spec(...))]` - Specification Attributes

Mark spec-only code with `#[mode(spec)]`. Parameterized spec attributes (axioms, datatype invariants, loop invariants, spec inclusion, and extra Boogie files) go in a companion `#[ext(spec(...))]` attribute, which requires `#[mode(spec)]` on the same item.

| Parameter | Description |
|-----------|-------------|
| `(axiom)` | Axiom definition |
| `(inv_target = <TYPE>)` | Datatype invariant for specified type |
| `(loop_inv(target = <FUNC>))` | External loop invariant |
| `(loop_inv(target = <FUNC>, label = N))` | Loop invariant with label |
| `(include = <PATH>)` | Include spec module |
| `(include(a = <PATH>, b = <PATH>))` | Include multiple spec modules (inner keys arbitrary but unique) |
| `(extra_bpl = b"<file>")` | Load extra Boogie code |
| `(extra_bpl(a = b"<file>", b = b"<file>"))` | Load multiple extra Boogie files (inner keys arbitrary but unique) |

Examples:
```move
use project::numbers::PositiveNumber;

#[mode(spec), ext(spec(axiom))]
fun sqrt_axiom(x: u64): u64 { ... }

#[mode(spec), ext(spec(inv_target = project::numbers::PositiveNumber))]
public fun PositiveNumber_inv(self: &PositiveNumber): bool {
    self.value() > 0
}

#[mode(spec), ext(spec(loop_inv(target = my_func_spec)))]
fun loop_inv_for_my_func() { }
```

## Loop Invariants

Loop invariants are required when a spec has conditions over variables modified inside a loop. There are two styles: inline and external.

### Inline Loop Invariants

Use the `invariant!` macro directly before a loop:

```move
#[spec(prove)]
fun sum_to_n_spec(n: u64): u128 {
    let mut sum: u128 = 0;
    let mut i: u64 = 0;

    invariant!(|| {
        ensures(i <= n);
        ensures(sum == (i as u128) * ((i as u128) + 1) / 2);
    });
    while (i < n) {
        i = i + 1;
        sum = sum + (i as u128);
    };

    ensures(sum == (n as u128) * ((n as u128) + 1) / 2);
    sum
}
```

### External Loop Invariants

Alternatively, define loop invariants as separate functions with `#[mode(spec), ext(spec(loop_inv(target = ...)))]`. The invariant function returns a boolean conjunction of all conditions.

```move
#[mode(spec), ext(spec(loop_inv(target = sum_to_n_spec)))]
#[ext(no_abort)]
fun sum_loop_inv(i: u64, n: u64, sum: u128): bool {
    i <= n && sum == (i as u128) * ((i as u128) + 1) / 2
}

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
- Invariant function parameters must match the loop variables
- Return a `bool` with conditions joined by `&&`
- Add `#[ext(no_abort)]` or `#[ext(pure)]` attribute
- For cloned values, use `__old_` prefix in parameter names (e.g., `__old_n` for `clone!(&n)`)
- For multiple loops, use `label = N` (0-indexed):

```move
#[mode(spec), ext(spec(loop_inv(target = my_spec, label = 0)))]
#[ext(no_abort)]
fun first_loop_inv(...): bool { ... }

#[mode(spec), ext(spec(loop_inv(target = my_spec, label = 1)))]
#[ext(no_abort)]
fun second_loop_inv(...): bool { ... }
```

## Datatype Invariants

Add any private-state accessor to the implementation module:

```move
module project::numbers;

public struct PositiveNumber { value: u64 }

#[test_only]
#[ext(pure)]
public fun value(self: &PositiveNumber): u64 {
    self.value
}
```

Define the invariant in the sibling spec package and target the implementation type:

```move
module project_specs::number_specs;

use project::numbers::PositiveNumber;

#[mode(spec), ext(spec(inv_target = project::numbers::PositiveNumber))]
public fun PositiveNumber_inv(self: &PositiveNumber): bool {
    self.value() > 0
}
```

The invariant is automatically checked on construction and modification.

## Quantifiers (`forall!` and `exists!`)

The `forall!` and `exists!` macros express universal and existential quantification
over all valid values of a type.

```
forall!<T>(|x| predicate(x))   // true if predicate holds for every value of T
exists!<T>(|x| predicate(x))   // true if predicate holds for at least one value of T
```

**Lambda parameter is a reference.** Inside the lambda, `x` has type `&T`. Pass it
directly to functions that take `&T`, or dereference with `*x` when a value is needed.

**The lambda must call a named pure function.** Inline expressions like `|x| *x + 10`
are not supported — the lambda body must be a call to a function annotated with
`#[ext(pure)]`.

### Pure predicate functions

Functions used as quantifier predicates must be annotated `#[ext(pure)]`. A pure
function:

- Must not abort (no `assert!`, no arithmetic overflow, no out-of-bounds access)
- Must be deterministic (no randomness or other non-deterministic operations)
- Takes its quantified argument as `&T`

```move
#[ext(pure)]
fun is_gte_0(x: &u64): bool {
    *x >= 0
}

#[ext(pure)]
fun is_10(x: &u64): bool {
    x == 10    // comparing &u64 with u64 is supported
}
```

### Basic usage

```move
#[spec(prove)]
fun quantifier_example_spec() {
    // All u64 values are >= 0 (trivially true)
    ensures(forall!<u64>(|x| is_gte_0(x)));

    // There exists a u64 equal to 10
    ensures(exists!<u64>(|x| is_10(x)));
}
```

### Extra captured arguments

Predicate functions can take additional parameters beyond the quantified variable.
Values from the enclosing scope are passed as extra arguments in the lambda call:

```move
#[ext(pure)]
fun is_greater_or_equal(a: u64, x: u64, b: u64): bool {
    x >= a && x >= b
}

#[spec(prove)]
fun extra_args_spec(a: u64, b: u64) {
    // For some x: x >= a AND x >= b
    ensures(exists!<u64>(|x| is_greater_or_equal(a, *x, b)));
}
```

Note that `a` and `b` come from the spec function's scope, while `*x` is the
quantified variable (dereferenced because `is_greater_or_equal` takes `u64`, not `&u64`).

### Using quantifiers in invariants

Quantifiers can appear in `requires`, `ensures`, and `invariant` expressions:

```move
#[ext(pure)]
fun invariant_expression(j: u64, i: u64, u: &vector<u8>, v: &vector<u8>): bool {
    j <= i && j < u.length() && i < v.length() && u[j] > v[i]
}

#[spec(prove, target = project::vectors::vec_leq)]
fun vec_leq_spec(i: u64): bool {
    requires(i < 4);

    let v: vector<u8> = vector[10, 20, 30, 40];
    let u: vector<u8> = vector[15, 25, 35, 45];

    let res = project::vectors::vec_leq(i);

    // For any i, there exists j <= i such that u[j] > v[i].
    ensures(res == exists!<u64>(|j| invariant_expression(*j, i, &u, &v)));
    res
}
```

### Common mistakes

| Mistake | Why it fails |
|---------|-------------|
| `\|x\| *x + 10` | Inline expression — must call a named pure function |
| Predicate uses `assert!` | Pure functions must not abort |
| Predicate calls non-deterministic code | Pure functions must be deterministic |
| Forgetting `#[ext(pure)]` on predicate | Predicate will not be recognized as pure |
