module 0x42::opaque_tests;

use prover::prover::{ensures};

fun add_wrap_buggy(x: u64, y: u64): u64 {
    x + y
}

#[spec]
fun add_wrap_buggy_spec(x: u64, y: u64): u64 {
    let result = add_wrap_buggy(x, y);
    ensures(result == x.to_int().add(y.to_int()).to_u64());
    result
}
