module 0x42::foo;

use prover::prover::ensures;

// #[ext(pure, uninterpreted)] makes bar globally uninterpreted in all specs by default
#[ext(pure, uninterpreted)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

// bar() == bar() holds even when uninterpreted (same symbolic value on both sides)
#[spec(prove)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == bar());
    result
}
