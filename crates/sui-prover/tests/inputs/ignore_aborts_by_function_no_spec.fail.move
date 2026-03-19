module 0x42::foo;

use prover::prover;

fun foo(x: u64): u64 {
    bar(x)
}

fun bar(x: u64): u64 {
    x + 1
}

#[spec(prove)]
fun foo_spec(x: u64): u64 {
    prover::asserts(prover::asserts_of(b"bar"));
    foo(x)
}
