module 0x42::foo;

use prover::prover;

fun foo(x: u64): u64 {
    x
}

fun bar(x: u64): u64 {
    x
}

#[spec(prove)]
fun foo_spec(x: u64): u64 {
    let result = foo(x);
    prover::ensures(result < bar(x));
    result
}

#[spec(prove)]
fun bar_spec(x: u64): u64 {
    let result = bar(x);
    prover::ensures(result < foo(x));
    result
}
