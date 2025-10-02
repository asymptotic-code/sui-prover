module 0x42::simple_max_succeeds_test;

#[spec_only]
use prover::prover::{ensures};

#[ext(pure)]
public fun simple_max(a: u64, b: u64): u64 {
    if (a >= b) {
        a
    } else {
        b
    }
}

#[spec(prove)]
fun simple_max_spec(a: u64, b: u64): u64 {
    let result = simple_max(a, b);

    ensures(result >= a);
    ensures(result >= b);
    ensures(result == a || result == b);

    result
}
