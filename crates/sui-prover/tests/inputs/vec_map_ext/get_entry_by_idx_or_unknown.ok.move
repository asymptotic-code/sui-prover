#[allow(unused)]
module 0x42::vec_map_ext_get_entry_by_idx_or_unknown_ok;

use sui::vec_map;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use sui::vec_map::get_entry_by_idx_or_unknown;

// In-range: get_entry_by_idx_or_unknown agrees with vec_map::get_entry_by_idx.
#[spec(prove)]
fun test_in_range_matches(m: &vec_map::VecMap<u64, u8>, i: u64) {
    requires(i < m.length());
    let (k1, v1) = get_entry_by_idx_or_unknown(m, i);
    let (k2, v2) = m.get_entry_by_idx(i);
    ensures(k1 == k2);
    ensures(v1 == v2);
}
