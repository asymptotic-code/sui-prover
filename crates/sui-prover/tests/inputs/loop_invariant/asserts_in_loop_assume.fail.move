module 0x42::loop_invariant_asserts_assume;

use prover::prover::{ensures, asserts, invariant};

// The function-level `asserts(n <= 100)` is exact: the impl aborts iff
// `n > 100`. The invariant `i <= n` is enough for the Check direction
// (with `n <= 100`, the body's `i < 100` follows from `i < n <= 100`),
// but not for the Assume direction. To close the Assume gap, the
// invariant would need to also ensure `i <= 100` — that is, the fact
// that the per-iteration assert has held for all completed iterations.
// Without that, the prover cannot conclude from a single symbolic loop
// body that the loop will *necessarily* abort when `n > 100`.

fun bounded_loop(n: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
    });
    while (i < n) {
        assert!(i < 100);
        i = i + 1;
    };
}

#[spec(prove)]
fun bounded_loop_spec(n: u64) {
    asserts(n <= 100);
    bounded_loop(n);
}
