// Demonstrates boogie_allow_path_isolation + isolate_paths boogie_opt.
// The branch is marked for path isolation, and boogie_opt = b"isolate_paths"
// makes all ensures in the spec use {:isolate "paths"} — one VC per
// path through the marked branch.

module 0x42::path_isolation;

use prover::prover::{ensures, boogie_allow_path_isolation};

fun pick_smaller(a: u64, b: u64): u64 {
    boogie_allow_path_isolation();
    if (a <= b) { a } else { b }
}

#[spec(prove, boogie_opt = b"isolate_paths")]
fun pick_smaller_spec(a: u64, b: u64): u64 {
    let r = pick_smaller(a, b);
    ensures(r <= a && r <= b);
    ensures(r == a || r == b);
    r
}
