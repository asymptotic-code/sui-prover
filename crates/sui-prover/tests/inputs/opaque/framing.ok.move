module 0x42::opaque_framing;

use prover::prover::{ensures, requires};

// verifies that a spec for a function mutating one element of a vector
// does not prevent proving that other elements are unchanged (framing).
fun set(x: &mut u8) {
    *x = 0
}

#[spec(prove)]
fun set_spec(x: &mut u8) {
    set(x)
}

#[spec(prove, focus)]
fun frame(v: &mut vector<u8>, i: u64, j: u64) {
    requires(j < v.length());
    requires(i < j);
    let vj = v[j];
    set(&mut v[i]);
    ensures(v[j] == vj);
}
