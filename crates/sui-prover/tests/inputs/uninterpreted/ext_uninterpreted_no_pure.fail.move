module 0x42::foo;

use prover::prover::ensures;

#[ext(uninterpreted)] // error: must also have #[ext(pure)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

#[spec(prove)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42);
    result
}
