module 0x42::foo;

#[spec_only]
use prover::prover::{ensures,asserts};

fun foo(a: u128): bool {
    a >= 0
}

#[spec(prove, ignore_abort)]
fun foo_spec(a: u128): bool {
    asserts(a > 0);
    let res = foo(a);
    ensures(true);
    res
}
