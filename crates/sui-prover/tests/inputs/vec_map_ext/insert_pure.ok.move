#[allow(unused)]
module 0x42::vec_map_ext_insert_pure_ok;

use sui::vec_map;

#[spec_only]
use prover::prover::{ensures, requires, clone};

#[spec_only]
use sui::vec_map::insert_pure;

// After insert, the functional model equals the mutable result.
#[spec(prove)]
fun test_insert_matches(m: &mut vec_map::VecMap<u64, u8>, k: u64, v: u8) {
    requires(!m.contains(&k));
    let old_m = clone!(m);
    m.insert(k, v);
    ensures(*m == *insert_pure(old_m, &k, &v));
}
