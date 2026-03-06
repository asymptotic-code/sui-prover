module 0x42::foo;

use prover::prover::ensures;

// bar is pure but NOT globally uninterpreted
#[ext(pure)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

// interpreted=bar should fail because bar is not marked #[ext(uninterpreted)]
#[spec(prove, interpreted = bar)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42);
    result
}
