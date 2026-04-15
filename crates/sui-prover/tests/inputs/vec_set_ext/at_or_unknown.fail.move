#[allow(unused)]
module 0x42::vec_set_ext_at_or_unknown_fail;

use sui::vec_set;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vec_set_ext::at_or_unknown;

// For an out-of-range index, at_or_unknown returns an uninterpreted value —
// claiming a specific value must fail to verify.
#[spec(prove)]
fun test_out_of_range_not_specific(s: &vec_set::VecSet<u64>, i: u64) {
    requires(i >= s.length());
    ensures(*at_or_unknown(s, i) == 0);
}
