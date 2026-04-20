module 0x42::asserts_loop_nested_fail;

use prover::prover::{ensures, asserts, invariant};

// Same nested-loop body as `asserts_loop_nested.move` but using bounded
// asserts (`n <= 100 && (n == 0 || m <= 200)`) instead of the
// forall-with-guard formulation.
//
// The Check direction works. The Assume direction fails: the prover
// cannot connect a single conjunctive assertion at the spec entry to
// the per-iteration abort behaviour spread across two nested loops.
//
// The fix is to express the asserts as `forall k, outer_safe(k, n, m)`
// and accumulate `forall k, k >= i || outer_safe(k, n, m)` in the
// outer loop invariant — the same vacuous-at-zero / collapses-at-exit
// pattern that works for `positive_check` and `increment_all`.

fun nested(n: u64, m: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 100);
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
    asserts(n <= 100 && (n == 0 || m <= 200));
    nested(n, m);
}
