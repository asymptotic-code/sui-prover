/// Alternate repro from https://github.com/asymptotic-code/sui-prover/issues/452
/// Matching on an enum inside a pure function reports a misleading loop error.
module 0x42::issue_452_match;

use prover::prover::ensures;

public enum E has copy, drop {
    A,
    B(u8),
}

#[ext(pure)]
public fun f(e: E): bool {
    match (e) {
        E::A => true,
        E::B(v) => v > 0,
    }
}

#[spec(prove)]
fun test() {
    ensures(f(E::B(1)))
}
