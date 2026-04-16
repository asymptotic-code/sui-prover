#[allow(unused)]
module 0x42::table_ext_borrow_or_unknown_ok;

use sui::table::Table;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use sui::table::borrow_or_unknown;

// Contained key: borrow_or_unknown agrees with table::borrow.
#[spec(prove)]
fun test_contained_matches_borrow(t: &Table<u64, u8>, k: u64) {
    requires(t.contains(k));
    ensures(borrow_or_unknown(t, k) == t.borrow(k));
}
