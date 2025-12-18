module 0x42::opaque_tests;

use prover::prover::{requires, ensures, asserts, clone};
use std::u64;

public struct Range<phantom T> {
    x: u64,
    y: u64,
}

fun scale<T>(r: &mut Range<T>, k: u64) {
    r.x = r.x * k;
    r.y = r.y * k;
}

#[spec(prove)]
fun scale_spec<T>(r: &mut Range<T>, k: u64) {
    let old_r = clone!(r);

    requires(r.x <= r.y);

    asserts(r.y.to_int().mul(k.to_int()).lte(u64::max_value!().to_int()));

    scale(r, k);

    ensures(r.x == old_r.x * k);
    ensures(r.y == old_r.y * k);
}
