#[allow(unused)]
module 0x42::quantifiers_partial_pattern_forall_fail;

#[mode(spec)]
use prover::prover::{begin_forall_lambda, ensures};

#[spec(prove)]
fun test_2_spec() {
    let positive = begin_forall_lambda();
    ensures(*positive);
}

// Should fail
