module 0x42::foo;

use prover::prover::ensures;

fun foo(x: u64): u64 {
    x + 1
}

#[spec(prove, ignore_abort, no_opaque)]
fun foo_spec(x: u64): u64 {
    let result = foo(x);
    ensures(result > x);
    result
}
