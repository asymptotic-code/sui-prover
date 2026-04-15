#[allow(unused)]
module 0x42::table_ext_borrow_or_unknown_fail;

use sui::table::Table;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::table_ext::borrow_or_unknown;

// For an absent key, borrow_or_unknown returns an uninterpreted value —
// claiming a specific value must fail to verify.
#[spec(prove)]
fun test_absent_not_specific(t: &Table<u64, u8>, k: u64) {
    requires(!t.contains(k));
    ensures(*borrow_or_unknown(t, k) == 0);
}
