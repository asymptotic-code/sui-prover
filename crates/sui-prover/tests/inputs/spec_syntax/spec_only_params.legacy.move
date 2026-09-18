// Every `spec_only` parameter, in the deprecated #[spec_only(...)] syntax.
// spec_only_params.new.move is the same file in the new syntax; outputs must match.
module 0x42::spec_only_params;

#[spec_only]
use prover::prover::{ensures, asserts};

public struct Counter has drop { value: u64 }

public struct Limit has drop { max: u64 }

// A datatype invariant, found by the `<Struct>_inv` name.
#[spec_only]
fun Counter_inv(c: &Counter): bool { c.value <= 100 }

// A datatype invariant with an explicit target.
#[spec_only(inv_target = 0x42::spec_only_params::Limit)]
fun limit_is_positive(l: &Limit): bool { l.max > 0 }

// A spec-only helper.
#[spec_only]
fun at_most(c: &Counter, n: u64): bool { c.value <= n }

#[spec_only(axiom)]
fun sqrt_axiom(x: u64): bool {
    x > 4 && x.to_int().sqrt().gt(2u64.to_int())
}

public fun bump(c: &mut Counter) {
    if (c.value < 100) {
        c.value = c.value + 1
    }
}

public fun new_limit(max: u64): Limit {
    assert!(max > 0);
    Limit { max }
}

public fun noop() {}

public fun count(x: u8, z: u8) {
    let mut y = 0;
    while (y < x) {
        y = y + 1;
    };
    let mut i = z;
    while (i > y) {
        i = i - 1;
    }
}

#[spec_only(loop_inv(target = count, label = 0)), ext(pure)]
fun count_inv_0(y: u8, x: u8): bool {
    y <= x
}

#[spec_only(loop_inv(target = count, label = 1)), ext(pure)]
fun count_inv_1(i: u8, z: u8): bool {
    i <= z
}

#[spec(prove)]
fun bump_spec(c: &mut Counter) {
    bump(c);
    ensures(at_most(c, 100));
}

#[spec(prove)]
fun new_limit_spec(max: u64): Limit {
    asserts(max > 0);
    new_limit(max)
}

#[spec(prove)]
fun noop_spec() {
    noop();
    ensures(16012031023u64.to_int().sqrt().gt(2u64.to_int()));
}

#[spec(prove)]
fun count_spec(x: u8, z: u8) {
    count(x, z)
}
