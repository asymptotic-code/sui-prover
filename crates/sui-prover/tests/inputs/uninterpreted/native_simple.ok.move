module 0x42::foo;

use prover::prover::ensures;

#[mode(spec), ext(spec_only, pure)]
native fun bar(): u64;

fun foo(): u64 {
    bar()
}

#[mode(spec), ext(spec(prove, uninterpreted = bar))]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == bar()); // should pass: both calls uninterpreted, same result
    result
}
