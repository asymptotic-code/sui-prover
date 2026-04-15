#[allow(unused)]
module 0x42::vector_ext_append_pure_ok;

#[spec_only]
use prover::prover::{ensures, clone};

#[spec_only]
use prover::vector_ext::append_pure;

#[spec(prove)]
fun test_append_matches(v1: &mut vector<u64>, v2: vector<u64>) {
    let old_v1 = clone!(v1);
    let old_v2 = clone!(&v2);
    v1.append(v2);
    ensures(*v1 == *append_pure(old_v1, old_v2));
}
