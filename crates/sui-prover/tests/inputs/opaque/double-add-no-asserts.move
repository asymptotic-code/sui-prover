module 0x42::opaque_tests;

use prover::prover::ensures;

fun add_no_asserts(x: u64, y: u64): u64 {
    x + y
}

fun double_no_asserts(x: u64): u64 {
    add_no_asserts(x, x)
}

#[spec(prove, ignore_abort)]
fun double_no_asserts_spec(x: u64): u64 {
    let result = double_no_asserts(x);

    ensures(result.to_int() == x.to_int().mul(2u64.to_int()));

    result
}
