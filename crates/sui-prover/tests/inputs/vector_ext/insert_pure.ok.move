#[allow(unused)]
module 0x42::vector_ext_insert_pure_ok;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use std::vector::insert_pure;

#[spec(prove)]
fun test_insert_matches(v: &mut vector<u64>, e: u64, i: u64) {
    requires(i <= vector::length(v));
    let old_v = clone!(v);
    v.insert(e, i);
    ensures(*v == *insert_pure(old_v, &e, i));
}
