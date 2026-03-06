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

// bar() == 42 cannot be proved when bar is globally uninterpreted
#[spec(prove)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42); // should fail: bar is uninterpreted, value unknown
    result
}
