#[allow(unused)]
module 0x42::object_table_ext_borrow_or_unknown_ok;

use sui::object_table::ObjectTable;

#[mode(spec), ext(spec_only)]
use prover::prover::{ensures, requires};

#[mode(spec), ext(spec_only)]
use sui::object_table::borrow_or_unknown;

public struct Foo has key, store {
    id: UID,
}

// Contained key: borrow_or_unknown agrees with object_table::borrow.
#[mode(spec), ext(spec(prove))]
fun test_contained_matches_borrow(t: &ObjectTable<u64, Foo>, k: u64) {
    requires(t.contains(k));
    ensures(borrow_or_unknown(t, k) == t.borrow(k));
}
