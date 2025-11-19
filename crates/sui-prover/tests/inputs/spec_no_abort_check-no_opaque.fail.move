module 0x42::foo;

use prover::prover::{requires, ensures};

fun foo(x: u64): u64 {
    x + 1
}

#[spec(prove, no_opaque)]
fun foo_spec(x: u64): u64 {
    requires(x < 100);
    let res = foo(x);
    ensures(res - 1 == x);
    res
}
