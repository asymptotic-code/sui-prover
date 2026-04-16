#[allow(unused)]
module 0x42::dynamic_field_ext_borrow_or_unknown_ok;

use sui::dynamic_field;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use sui::dynamic_field::borrow_or_unknown;

public struct Foo has key {
    id: UID,
}

// Present field: borrow_or_unknown agrees with dynamic_field::borrow.
#[spec(prove)]
fun test_present_matches_borrow(x: &Foo, k: u64) {
    requires(dynamic_field::exists_with_type<u64, u8>(&x.id, k));
    ensures(borrow_or_unknown<u64, u8>(&x.id, k) == dynamic_field::borrow<u64, u8>(&x.id, k));
}
