module 0x42::foo;

use prover::prover::ensures;

// bar is globally uninterpreted: all specs treat it as uninterpreted by default
#[ext(pure, uninterpreted)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

#[spec(prove)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42); // should fail: bar is globally uninterpreted
    result
}
