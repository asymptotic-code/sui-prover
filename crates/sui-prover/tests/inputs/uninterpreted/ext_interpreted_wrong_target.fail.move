module 0x42::foo;

use prover::prover::ensures;

// bar is NOT globally uninterpreted (no #[ext(uninterpreted)])
#[ext(pure)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

// Error: interpreted=bar target must be globally uninterpreted
#[spec(prove, interpreted = bar)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42);
    result
}
