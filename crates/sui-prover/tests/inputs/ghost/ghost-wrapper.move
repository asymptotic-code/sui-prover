module 0x42::ghost_tests;

use prover::ghost;
use prover::prover::ensures;
use std::u64;

public struct GhostStruct {}

public struct Wrapper<T> {
    value: T,
}

#[spec(prove)]
fun wrapper_well_formed_spec() {
    ghost::declare_global<GhostStruct, Wrapper<u64>>();
    ensures(ghost::global<GhostStruct, Wrapper<u64>>().value <= u64::max_value!());
}
