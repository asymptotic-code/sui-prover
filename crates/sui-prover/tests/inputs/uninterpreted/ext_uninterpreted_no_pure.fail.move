module 0x42::foo;

use prover::prover::ensures;

// #[ext(uninterpreted)] without #[ext(pure)] should emit an error
#[ext(uninterpreted)]
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
