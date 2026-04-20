module 0x42::asserts_loop_nested;

use prover::prover::{ensures, asserts, invariant, forall};

// Nested loops where each body has its own per-iteration assertion.
// The function-level asserts is a forall over the outer iteration index,
// stating per-iteration safety: the outer body's `i < 100` AND the inner
// body's `j < 200` (which only matters when the inner loop runs).
//
// The outer loop invariant uses the standard `k < i` guard so it is
// vacuous at iteration 0 and accumulates per-iteration. At loop exit
// `i == n`, the invariant collapses to the function-level asserts,
// contradicting `!asserts` and forcing abort under the Assume direction.
//
// This is the same pattern that works for `positive_check` in
// `asserts_in_loop.move` and `increment_all` in
// `asserts_loop_mutating_quantified.move`, applied to nested loops.

#[ext(pure)]
fun outer_safe(k: u64, n: u64, m: u64): bool {
    k >= n || (k < 100 && m <= 200)
}

#[ext(pure)]
fun visited_outer_safe(k: u64, i: u64, n: u64, m: u64): bool {
    k >= i || outer_safe(k, n, m)
}

fun nested(n: u64, m: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(forall!(|k| visited_outer_safe(*k, i, n, m)));
    });
    while (i < n) {
        assert!(i < 100);
        let mut j: u64 = 0;
        invariant!(|| {
            ensures(j <= m);
            ensures(j <= 200);
        });
        while (j < m) {
            assert!(j < 200);
            j = j + 1;
        };
        i = i + 1;
    };
}

#[spec(prove)]
fun nested_spec(n: u64, m: u64) {
    asserts(forall!(|k| outer_safe(*k, n, m)));
    nested(n, m);
}
