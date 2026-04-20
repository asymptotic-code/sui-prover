module 0x42::loop_invariant_asserts_missing;

use prover::prover::{ensures, invariant};

// Test 1 from `asserts_in_loop.move` with the function-level
// `asserts(n <= 100)` removed from the spec. The body's `assert!(i < 100)`
// can fail when `n > 100`, so the impl can abort but the spec does not
// declare it. Should fail with "code should not abort".

fun bounded_loop_no_asserts(n: u64) {
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
fun bounded_loop_no_asserts_spec(n: u64) {
    bounded_loop_no_asserts(n);
}
