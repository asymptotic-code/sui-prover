#[allow(unused)]
module 0x42::vec_map_ext_get_entry_by_idx_or_unknown_fail;

use sui::vec_map;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vec_map_ext::get_entry_by_idx_or_unknown;

// For an out-of-range index, get_entry_by_idx_or_unknown returns an
// uninterpreted pair — claiming a specific value must fail to verify.
#[spec(prove)]
fun test_out_of_range_not_specific(m: &vec_map::VecMap<u64, u8>, i: u64) {
    requires(i >= m.length());
    let (_k, v) = get_entry_by_idx_or_unknown(m, i);
    ensures(*v == 0);
}
