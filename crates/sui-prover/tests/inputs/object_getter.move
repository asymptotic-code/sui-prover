module 0x42::object_test;

use prover::prover::{requires, ensures};

public struct Str1 has key {
    id: UID,
    value: u64
}

fun struct_value(self: &Str1): u64 {
    self.value
}

#[spec(prove)]
fun struct_value_spec(self: &Str1): u64 {
    let r = struct_value(self);
    r
}

#[spec(prove)] // fails without deterministic analysis
fun my_spec(s1: &Str1, s2: &Str1) {
    requires(s1 == s2);
    ensures(struct_value(s1) == struct_value(s2))
}
