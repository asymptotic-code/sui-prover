module 0x42::object_id_test;

use prover::prover::{requires, ensures};

public struct S has key, store {
    id: UID,
}

// Test object::id with different objects
#[spec(prove)]
fun different_objects_spec(s1: &S, s2: &S) {
    requires(s1 != s2);
    ensures(object::id(s1) != object::id(s2));
}
