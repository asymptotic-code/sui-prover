module 0x42::foo;

use prover::prover::ensures;

#[ext(pure)]
#[spec_only]
native fun bar(): u64;

fun foo(): u64 {
    bar()
}

#[spec(prove, uninterpreted = bar)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == bar()); // should pass: both calls uninterpreted, same result
    result
}
