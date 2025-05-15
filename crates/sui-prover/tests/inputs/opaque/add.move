module 0x42::opaque_tests;

use prover::prover::{ensures, asserts};
use std::u64;

fun add(x: u64, y: u64): u64 {
    x + y
}

#[spec(prove)]
fun add_spec(x: u64, y: u64): u64 {
    asserts((x as u128) + (y as u128) <= u64::max_value!() as u128);

    let result = add(x, y);

    ensures(result == x + y);

    result
}
