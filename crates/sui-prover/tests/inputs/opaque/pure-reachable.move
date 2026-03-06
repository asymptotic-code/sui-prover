/// Test that pure functions which are only "reachable" (not "inlined") get
/// inlined $pure bodies in Boogie, rather than bodyless uninterpreted declarations.
///
/// `get_value` has a spec with `#[spec(skip)]`, making it only "reachable".
/// Previously, `get_value$pure` was emitted as a bodyless Boogie function,
/// causing Z3 to treat it as uninterpreted and potentially returning invalid values.
/// Now reachable pure functions get inlined bodies, so `get_value$pure(box)`
/// correctly resolves to `box.value`.
module 0x42::opaque_tests;

use prover::prover::ensures;

public struct Box has copy, drop {
    value: u64,
}

#[ext(pure)]
fun get_value(b: &Box): u64 {
    b.value
}

// The skip attribute makes get_value only "reachable" (not "inlined")
#[spec(skip, target = get_value)]
fun get_value_spec(b: &Box): u64 {
    let result = get_value(b);
    ensures(result == b.value);
    result
}

fun set_value(b: &mut Box, v: u64) {
    b.value = v;
}

#[spec(prove, target = set_value)]
fun set_value_spec(b: &mut Box, v: u64) {
    set_value(b, v);
    // This ensures relies on get_value$pure having a body that resolves
    // to b.value. If get_value$pure were uninterpreted, Z3 could return
    // any value and this assertion might fail.
    ensures(get_value(b) == v);
}
