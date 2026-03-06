// Test that #[ext(uninterpreted)] makes a function globally uninterpreted by default.
// The spec fails because bar() is uninterpreted; we cannot prove bar() == 42.
module 0x42::foo;

use prover::prover::ensures;

#[ext(pure, uninterpreted)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

// No need to write uninterpreted = bar; bar is globally uninterpreted via #[ext(uninterpreted)]
#[spec(prove)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42); // should fail: bar is uninterpreted by default
    result
}
