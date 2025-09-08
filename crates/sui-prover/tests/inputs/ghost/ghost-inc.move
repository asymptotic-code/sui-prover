module 0x42::ghost_tests;

use prover::ghost;
use prover::prover::{requires, ensures, asserts};
use std::u64;

public struct GhostStruct {}

fun inc(x: u64): u64 {
    x + 1
}

fun inc_saturated(x: u64): u64 {
    if (x == u64::max_value!()) {
        x
    } else {
        inc(x)
    }
}

#[spec]
fun inc_spec(x: u64): u64 {
    ghost::declare_global_mut<GhostStruct, bool>();
    requires(ghost::global<GhostStruct, _>() == false);

    asserts((x as u128) + 1 <= u64::max_value!() as u128);

    let result = inc(x);

    ensures(result == x + 1);
    ensures(ghost::global<GhostStruct, _>() == true);

    result
}

#[spec(prove)]
fun inc_saturated_spec(x: u64): u64 {
    ghost::declare_global_mut<GhostStruct, bool>();
    requires(ghost::global<GhostStruct, _>() == false);

    let result = inc_saturated(x);

    ensures((ghost::global<GhostStruct, _>() == true) == (x != u64::max_value!()));

    result
}