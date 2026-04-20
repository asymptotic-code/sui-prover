module 0x42::loop_invariant_asserts_weak_inv;

use prover::prover::{ensures, asserts, invariant};

// Test 2 from `asserts_in_loop.move` with the invariant weakened: it no
// longer ties `x` to its initial value, so even with the function-level
// asserts holding at entry, the prover cannot show that `x - 1` stays in
// range across iterations. Should fail with "code should not abort".

fun decrement_loop_weak(mut x: u64, n: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
    });
    while (i < n) {
        x = x - 1;
        i = i + 1;
    };
}

#[spec(prove)]
fun decrement_loop_weak_spec(x: u64, n: u64) {
    asserts(x >= n);
    decrement_loop_weak(x, n);
}
