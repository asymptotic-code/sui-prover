/// Test that mutation framing works when a spec is provided for the called function.
/// Regression test for issue #545: mutation path was not preserved in opaque calls.
module 0x42::framing_vec;

use prover::prover::{ensures, requires};

fun set(x: &mut u8) {
    *x = 0
}

#[spec(prove)]
fun set_spec(x: &mut u8) {
    set(x)
}

/// Verifies that calling set(&mut v[i]) does not affect v[j] when i != j.
#[spec(prove, focus)]
fun frame(v: &mut vector<u8>, i: u64, j: u64) {
    requires(j < v.length());
    requires(i < j);
    let vj = v[j];
    set(&mut v[i]);
    ensures(v[j] == vj);
}
