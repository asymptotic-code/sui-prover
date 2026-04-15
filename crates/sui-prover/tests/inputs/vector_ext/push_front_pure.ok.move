#[allow(unused)]
module 0x42::vector_ext_push_front_pure_ok;

#[spec_only]
use prover::prover::{ensures, clone};

#[spec_only]
use prover::vector_ext::push_front_pure;

// Length of push_front result is length + 1.
#[spec(prove)]
fun test_push_front_length(v: &vector<u64>, e: u64) {
    ensures(
        vector::length(push_front_pure(v, &e)).to_int()
            == vector::length(v).to_int().add(1u64.to_int())
    );
}

// New first element equals the pushed element.
#[spec(prove)]
fun test_push_front_head(v: &vector<u64>, e: u64) {
    let r = push_front_pure(v, &e);
    ensures(*vector::borrow(r, 0) == e);
}
