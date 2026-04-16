// Uses prover::split_here() in the middle of an if-then-else function body
// to force Boogie to split the verification at that point. Without the
// annotation, Boogie would prove the post-condition as one VC; with it,
// the pre-split prefix and the post-split suffix are verified separately.

module 0x42::split_here_if_then_else;

use prover::prover::{ensures, implies, split_here};

fun clamp_and_scale(x: u64, lo: u64, hi: u64): u64 {
    // Phase 1: clamp into [lo, hi]
    let clamped = if (x < lo) {
        lo
    } else if (x > hi) {
        hi
    } else {
        x
    };

    // Split the VC between the clamp phase and the scale phase — gives Z3
    // two small problems instead of one big one.
    split_here();

    // Phase 2: saturating double
    if (clamped > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        clamped * 2
    }
}

#[spec(prove)]
fun clamp_and_scale_spec(x: u64, lo: u64, hi: u64): u64 {
    let r = clamp_and_scale(x, lo, hi);
    // Both phases contribute to the post-condition.
    ensures(implies(lo <= hi, r >= lo && r / 2 <= hi));
    r
}
