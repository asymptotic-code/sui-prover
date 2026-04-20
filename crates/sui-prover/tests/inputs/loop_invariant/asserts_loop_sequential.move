module 0x42::asserts_loop_sequential;

use prover::prover::{ensures, asserts, invariant};

// Two sequential loops in the same function, each with its own
// per-iteration assertion tied to a separate function-level asserts.
// Each invariant carries the corresponding "asserts-up-to-i" bound.

fun two_sequential_loops(n: u64, m: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 100);
    });
    while (i < n) {
        assert!(i < 100);
        i = i + 1;
    };
    let mut j: u64 = 0;
    invariant!(|| {
        ensures(j <= m);
        ensures(j <= 200);
    });
    while (j < m) {
        assert!(j < 200);
        j = j + 1;
    };
}

#[spec(prove)]
fun two_sequential_loops_spec(n: u64, m: u64) {
    asserts(n <= 100);
    asserts(m <= 200);
    two_sequential_loops(n, m);
}
