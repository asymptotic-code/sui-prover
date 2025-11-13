#[allow(unused)]
module 0x42::quantifiers_partial_pattern_fail;

#[spec_only]
use prover::prover::{begin_forall_lambda, end_exists_lambda, ensures};
#[spec_only]
use prover::vector_iter::{begin_map_lambda};

#[spec(prove)]
fun test_1_spec() {
    let v = vector[0u64, 10, 20, 10, 30];
    let x = begin_map_lambda<u64>(&v);
    ensures(*x > 0);
}

#[spec(prove)]
fun test_2_spec() {
    let positive = begin_forall_lambda();
    ensures(*positive);
}

#[spec(prove)]
fun test_3_spec() {
    let b = end_exists_lambda();
    ensures(b);
}

// All tests should fail
