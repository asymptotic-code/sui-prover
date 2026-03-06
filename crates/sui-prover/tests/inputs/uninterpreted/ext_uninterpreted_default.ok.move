// Test that #[ext(uninterpreted)] makes a function globally uninterpreted by default.
// The spec succeeds because bar() == bar() is a tautology even with uninterpreted bar.
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
    ensures(result == bar()); // should pass: both calls return the same uninterpreted value
    result
}
