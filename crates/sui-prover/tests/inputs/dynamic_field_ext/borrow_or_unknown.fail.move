#[allow(unused)]
module 0x42::dynamic_field_ext_borrow_or_unknown_fail;

use sui::dynamic_field;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::dynamic_field_ext::borrow_or_unknown;

public struct Foo has key {
    id: UID,
}

// For an absent dynamic field, borrow_or_unknown returns an uninterpreted
// value — claiming a specific value must fail to verify.
#[spec(prove)]
fun test_absent_not_specific(x: &Foo, k: u64) {
    requires(!dynamic_field::exists_with_type<u64, u8>(&x.id, k));
    ensures(*borrow_or_unknown<u64, u8>(&x.id, k) == 0);
}
