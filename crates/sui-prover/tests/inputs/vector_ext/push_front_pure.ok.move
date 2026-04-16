#[allow(unused)]
module 0x42::vector_ext_push_front_pure_ok;

#[spec_only]
use prover::prover::{ensures, clone};

#[spec_only]
use std::vector::push_front_pure;

// New first element equals the pushed element.
#[spec(prove)]
fun test_push_front_head(v: &vector<u64>, e: u64) {
    let r = push_front_pure(v, &e);
    ensures(*vector::borrow(r, 0) == e);
}
