module 0x42::asserts_loop_multi_assert;

use prover::prover::{ensures, asserts, invariant};

// Body has two `assert!` calls with different conditions. The
// function-level asserts is the conjunction of the per-iteration
// preconditions. The invariant carries the "asserts-up-to-i" fact for
// each independently — `i <= 100` and `i <= 50` (which is `i <= 50`
// when conjoined).

fun two_asserts_loop(n: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 50);
    });
    while (i < n) {
        assert!(i < 100);
        assert!(i * 2 < 100);
        i = i + 1;
    };
}

#[spec(prove)]
fun two_asserts_loop_spec(n: u64) {
    asserts(n <= 50);
    two_asserts_loop(n);
}
