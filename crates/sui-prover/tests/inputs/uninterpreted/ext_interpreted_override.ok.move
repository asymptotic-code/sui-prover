module 0x42::foo;

use prover::prover::ensures;

// bar is globally uninterpreted by default
#[ext(pure, uninterpreted)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

// Other specs can't prove bar() == 42 (it's uninterpreted by default)
#[spec(prove)]
fun foo_uninterpreted_spec(): u64 {
    let result = foo();
    ensures(result == bar()); // passes: same uninterpreted symbol on both sides
    result
}

// This spec uses interpreted=bar to override the global default and see bar's actual value
#[spec(prove, interpreted = bar)]
fun foo_interpreted_spec(): u64 {
    let result = foo();
    ensures(result == 42); // passes: bar is interpreted here, its body returns 42
    result
}
