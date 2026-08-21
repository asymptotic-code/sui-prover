#[allow(unused)]
module 0x42::vector_ext_pop_front_pure_ok;

#[mode(spec)]
use prover::prover::{ensures, requires};

#[mode(spec)]
use std::vector::pop_front_pure;

// Length of pop_front on a non-empty vector is length - 1.
#[spec(prove)]
fun test_pop_front_length(v: &vector<u64>) {
    requires(!v.is_empty());
    ensures(vector::length(pop_front_pure(v)) == vector::length(v) - 1);
}

// Empty vector: pop_front returns unchanged.
#[spec(prove)]
fun test_pop_front_empty(v: &vector<u64>) {
    requires(v.is_empty());
    ensures(pop_front_pure(v) == v);
}
