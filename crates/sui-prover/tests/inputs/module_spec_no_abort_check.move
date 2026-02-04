module 0x42::spec_basic;

use prover::prover::{ensures, requires};

fun foo(x: u64): u64 {
    x + 1
}

#[spec]
fun foo_spec(x: u64): u64 {
    let result = foo(x);
    ensures(result == x + 1);
    result
}

fun bar(x: u64): u64 {
    x + 2
}

#[spec(prove)]
fun bar_spec(x: u64): u64 {
    requires(x <= 10);
    let result = bar(x);
    ensures(result == x + 2);
    result
}
