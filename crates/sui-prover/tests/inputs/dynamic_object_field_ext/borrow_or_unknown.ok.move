#[allow(unused)]
module 0x42::dynamic_object_field_ext_borrow_or_unknown_ok;

use sui::dynamic_object_field;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use sui::dynamic_object_field::borrow_or_unknown;

public struct Parent has key {
    id: UID,
}

public struct Child has key, store {
    id: UID,
}

// Present field: borrow_or_unknown agrees with dynamic_object_field::borrow.
#[spec(prove)]
fun test_present_matches_borrow(x: &Parent, k: u64) {
    requires(dynamic_object_field::exists_with_type<u64, Child>(&x.id, k));
    ensures(
        borrow_or_unknown<u64, Child>(&x.id, k)
            == dynamic_object_field::borrow<u64, Child>(&x.id, k)
    );
}
