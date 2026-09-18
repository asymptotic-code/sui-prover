#[allow(unused)]
module 0x42::vec_map_ext_get_or_unknown_ok;

use sui::vec_map;

#[mode(spec), ext(spec_only)]
use prover::prover::{ensures, requires};

#[mode(spec), ext(spec_only)]
use sui::vec_map::get_or_unknown;

// Contained key: get_or_unknown agrees with vec_map::get.
#[mode(spec), ext(spec(prove))]
fun test_contained_matches_get(m: &vec_map::VecMap<u64, u8>, k: u64) {
    requires(m.contains(&k));
    ensures(get_or_unknown(m, &k) == m.get(&k));
}

#[mode(spec), ext(spec(prove))]
fun test_method_syntax(m: &vec_map::VecMap<u64, u8>, k: u64) {
    requires(m.contains(&k));
    ensures(m.get_or_unknown(&k) == m.get(&k));
}
