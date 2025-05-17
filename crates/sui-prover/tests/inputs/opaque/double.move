module 0x42::opaque_tests;

use prover::prover::{ensures, asserts};
use std::u64;

fun add(x: u64, y: u64): u64 {
    x + y
}

fun double(x: u64): u64 {
    add(x, x)
}

#[spec(prove)]
fun double_spec(x: u64): u64 {
    asserts((x as u128) * 2 <= u64::max_value!() as u128);

    let result = double(x);

    ensures(result == x * 2);

    result
}
