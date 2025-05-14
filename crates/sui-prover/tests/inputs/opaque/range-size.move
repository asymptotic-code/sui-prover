module 0x42::opaque_tests;

use prover::prover::{requires, ensures};

public struct Range<phantom T> {
    x: u64,
    y: u64,
}

fun size<T>(r: &Range<T>): u64 {
    r.y - r.x
}

#[spec(prove)]
fun size_spec<T>(r: &Range<T>): u64 {
    requires(r.x <= r.y);

    let result = size(r);

    ensures(result == r.y - r.x);

    result
}
