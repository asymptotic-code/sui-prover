#[allow(unused)]
module 0x42::quantifiers_partial_pattern_exists_fail;

#[mode(spec)]
use prover::prover::{end_exists_lambda, ensures};

#[spec(prove)]
fun test_3_spec() {
    let b = end_exists_lambda();
    ensures(b);
}

// Should fail
