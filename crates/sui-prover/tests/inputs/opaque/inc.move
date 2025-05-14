module 0x42::opaque_tests;

use prover::prover::{ensures, asserts};
use std::u64;

fun inc(x: u64): u64 {
    x + 1
}

#[spec(prove)]
fun inc_spec(x: u64): u64 {
    asserts((x as u128) + 1 <= u64::max_value!() as u128);

    let result = inc(x);

    ensures(result == x + 1);

    result
}
