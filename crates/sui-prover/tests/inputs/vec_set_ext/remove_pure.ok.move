#[allow(unused)]
module 0x42::vec_set_ext_remove_pure_ok;

use sui::vec_set;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use prover::vec_set_ext::remove_pure;

#[spec(prove)]
fun test_remove_matches(s: &mut vec_set::VecSet<u64>, k: u64) {
    requires(s.contains(&k));
    let old_s = clone!(s);
    s.remove(&k);
    ensures(*s == *remove_pure(old_s, &k));
}
