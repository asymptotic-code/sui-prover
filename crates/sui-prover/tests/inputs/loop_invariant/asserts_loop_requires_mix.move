module 0x42::asserts_loop_requires_mix;

use prover::prover::{ensures, requires, asserts, invariant};

// `requires` is an unconditional precondition (assumed by both the Check
// and Assume directions). `asserts` is the abort contract (must hold or
// the function aborts).
//
// Here `requires(n > 0)` rules out the empty-loop case from both
// verification directions, while `asserts(n <= 100)` is the per-iteration
// abort condition that the body's `assert!(i < 100)` would otherwise
// trigger.

fun bounded_loop_nonzero(n: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 100);
    });
    while (i < n) {
        assert!(i < 100);
        i = i + 1;
    };
}

#[spec(prove)]
fun bounded_loop_nonzero_spec(n: u64) {
    requires(n > 0);
    asserts(n <= 100);
    bounded_loop_nonzero(n);
}
