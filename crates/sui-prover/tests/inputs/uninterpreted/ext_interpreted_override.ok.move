module 0x42::foo;

use prover::prover::ensures;

// bar is globally uninterpreted by default
#[ext(pure, uninterpreted)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

// This spec uses interpreted=bar to override the global uninterpreted default.
// It can now prove bar() == 42.
#[spec(prove, interpreted = bar)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42); // passes: bar is interpreted here
    result
}
