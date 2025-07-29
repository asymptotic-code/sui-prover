module 0x42::foo;

#[spec_only]
use prover::prover::ensures;

fun foo(a: u128): bool {
    a >= 0
}

#[spec(prove, ignore_abort)]
fun scenario(a: u128): bool {
    let res = foo(a);
    assert!(false);
    ensures(true);
    res
}
