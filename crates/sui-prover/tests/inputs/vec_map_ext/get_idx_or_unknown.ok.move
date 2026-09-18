#[allow(unused)]
module 0x42::vec_map_ext_get_idx_or_unknown_ok;

use sui::vec_map;

#[mode(spec), ext(spec_only)]
use prover::prover::{ensures, requires};

#[mode(spec), ext(spec_only)]
use sui::vec_map::get_idx_or_unknown;

// Contained key: get_idx_or_unknown agrees with vec_map::get_idx.
#[mode(spec), ext(spec(prove))]
fun test_contained_matches(m: &vec_map::VecMap<u64, u8>, k: u64) {
    requires(m.contains(&k));
    ensures(get_idx_or_unknown(m, &k) == m.get_idx(&k));
}
