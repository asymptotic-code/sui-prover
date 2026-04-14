/// bar() is globally uninterpreted by default.
/// foo_spec_a cannot prove bar() == 42 (uninterpreted), but
/// foo_spec_b uses interpreted=bar to get the actual value and can prove bar() == 42.
module 0x42::foo;

use prover::prover::ensures;

#[ext(pure, uninterpreted)]
fun bar(): u64 {
    42
}

fun foo(): u64 {
    bar()
}

#[spec(prove, interpreted = bar)]
fun foo_spec(): u64 {
    let result = foo();
    ensures(result == 42); // passes: bar is interpreted here, so foo() == bar() == 42
    result
}
