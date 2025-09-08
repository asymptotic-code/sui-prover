module 0x42::opaque_tests;

use prover::prover::{ensures};

fun add_wrap_buggy(x: u64, y: u64): u64 {
    x + y
}

fun double_wrap_buggy(x: u64): u64 {
    add_wrap_buggy(x, x)
}

#[spec(prove)]
fun double_wrap_buggy_spec(x: u64): u64 {
    let result = double_wrap_buggy(x);
    ensures(result == x.to_int().mul((2 as u8).to_int()).to_u64());
    result
}
