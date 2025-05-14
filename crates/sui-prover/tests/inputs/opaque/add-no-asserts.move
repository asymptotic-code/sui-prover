module 0x42::opaque_tests;

use prover::prover::ensures;

fun add_no_asserts(x: u64, y: u64): u64 {
    x + y
}

#[spec(prove, ignore_abort)]
fun add_no_asserts_spec(x: u64, y: u64): u64 {
    let result = add_no_asserts(x, y);

    ensures(result.to_int() == x.to_int().add(y.to_int()));

    result
}
