#[allow(unused)]
module 0x42::vec_set_ext_insert_pure_ok;

use sui::vec_set;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use sui::vec_set::insert_pure;

#[spec(prove)]
fun test_insert_matches(s: &mut vec_set::VecSet<u64>, k: u64) {
    requires(!s.contains(&k));
    let old_s = clone!(s);
    s.insert(k);
    ensures(*s == *insert_pure(old_s, &k));
}
