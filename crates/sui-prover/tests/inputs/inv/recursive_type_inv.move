module 0x42::recursive_type_inv;

#[allow(unused_field)]
public struct Leaf has copy, drop, store {
    value: u64,
    left: Option<Leaf>,
    right: Option<Leaf>,
}

#[spec_only(inv_target=0x42::recursive_type_inv::Leaf)]
fun Leaf_inv(self: &Leaf): bool {
    self.value > 0
}

public struct A has copy, drop, store {
    value: u64,
    b_field: vector<B>,
}

public struct B has copy, drop, store {
    value: u64,
    c_field: vector<C>,
}

public struct C has copy, drop, store {
    value: u64,
    a_field: vector<A>,
}

public fun new_a(value: u64): A {
    A { value, b_field: vector[] }
}

public fun new_b(value: u64): B {
    B { value, c_field: vector[] }
}

public fun new_c(value: u64): C {
    C { value, a_field: vector[] }
}

#[spec_only(inv_target=0x42::recursive_type_inv::A)]
fun A_inv(self: &A): bool {
    self.value > 0
}

