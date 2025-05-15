module 0x42::opaque_tests;

use prover::prover::{ensures};

fun add_wrap(x: u64, y: u64): u64 {
    (((x as u128) + (y as u128)) % 18446744073709551616) as u64
}

fun double_wrap(x: u64): u64 {
    add_wrap(x, x)
}

#[spec(prove)]
fun double_wrap_spec(x: u64): u64 {
    let result = double_wrap(x);
    ensures(result == x.to_int().mul((2 as u8).to_int()).to_u64());
    result
}
