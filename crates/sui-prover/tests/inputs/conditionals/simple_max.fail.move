module 0x42::simple_max_failure_test;

#[spec_only]
use prover::prover::{ensures};

// A broken max function that returns the minimum instead (should fail verification)
#[ext(pure)]
public fun simple_max(a: u64, b: u64): u64 {
    if (a >= b) {
        b  // WRONG: should return a (the larger value)
    } else {
        a  // WRONG: should return b (the larger value)
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
