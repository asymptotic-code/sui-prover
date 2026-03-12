/// bar() is globally uninterpreted. The spec can prove bar() == bar() (reflexivity),
/// but cannot prove bar() == 42 (the actual implementation is hidden).
module 0x42::foo;

use prover::prover::ensures;

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
    ensures(result == bar()); // passes: both calls are the same uninterpreted value
    result
}
