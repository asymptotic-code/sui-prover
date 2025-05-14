module 0x42::ghost_tests;

use prover::ghost;
use prover::prover::ensures;

public struct GhostStruct {}

fun set_test() {
    ghost::set<GhostStruct, bool>(&true);
}

#[spec(prove)]
fun set_test_spec() {
    ghost::declare_global_mut<GhostStruct, bool>();
    set_test();
    ensures(ghost::global<GhostStruct, bool>() == true);
}
