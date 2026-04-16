// Demonstrates boogie_allow_path_isolation + boogie_isolate_paths.
// The branch is marked for path isolation: Boogie creates one VC per
// path through that branch for the isolated assertion.

module 0x42::path_isolation;

use prover::prover::{ensures, boogie_allow_path_isolation, boogie_isolate_paths};

fun pick_smaller(a: u64, b: u64): u64 {
    boogie_allow_path_isolation();
    if (a <= b) { a } else { b }
}

#[spec(prove)]
fun pick_smaller_spec(a: u64, b: u64): u64 {
    let r = pick_smaller(a, b);
    boogie_isolate_paths(r <= a && r <= b);
    ensures(r == a || r == b);
    r
}
