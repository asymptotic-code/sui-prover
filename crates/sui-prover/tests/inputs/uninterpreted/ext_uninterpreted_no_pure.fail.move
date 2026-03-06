// Test that #[ext(uninterpreted)] without #[ext(pure)] produces an error.
module 0x42::foo;

use prover::prover::ensures;

#[ext(uninterpreted)] // should fail: uninterpreted requires pure
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

#[spec(prove)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == bar());
    result
}
