#[allow(unused)]
module 0x42::vec_set_ext_at_or_unknown_ok;

use sui::vec_set;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vec_set_ext::at_or_unknown;

// In-range: at_or_unknown agrees with the key at insertion-order index.
#[spec(prove)]
fun test_in_range_matches(s: &vec_set::VecSet<u64>, i: u64) {
    requires(i < s.length());
    ensures(at_or_unknown(s, i) == s.keys().borrow(i));
}
