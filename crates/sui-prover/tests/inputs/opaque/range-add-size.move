module 0x42::opaque_tests;

use prover::prover::{requires, ensures, asserts};
use std::u64;

public struct Range<phantom T> {
    x: u64,
    y: u64,
}

fun size<T>(r: &Range<T>): u64 {
    r.y - r.x
}

fun add_size<T, U>(r1: &Range<T>, r2: &Range<U>): u64 {
    size(r1) + size(r2)
}

#[spec(prove)]
fun add_size_spec<T, U>(r1: &Range<T>, r2: &Range<U>): u64 {
    requires(r1.x <= r1.y);
    requires(r2.x <= r2.y);

    asserts(((r1.y - r1.x) as u128) + ((r2.y - r2.x) as u128) <= u64::max_value!() as u128);

    let result0 = add_size(r1, r2);

    ensures(result0 == (r1.y - r1.x) + (r2.y - r2.x));

    result0
}
