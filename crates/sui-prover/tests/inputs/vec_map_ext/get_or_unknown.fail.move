#[allow(unused)]
module 0x42::vec_map_ext_get_or_unknown_fail;

use sui::vec_map;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use sui::vec_map::get_or_unknown;

// For an absent key, get_or_unknown returns an uninterpreted value —
// claiming a specific value must fail to verify.
#[spec(prove)]
fun test_absent_not_specific(m: &vec_map::VecMap<u64, u8>, k: u64) {
    requires(!m.contains(&k));
    ensures(*get_or_unknown(m, &k) == 0);
}
