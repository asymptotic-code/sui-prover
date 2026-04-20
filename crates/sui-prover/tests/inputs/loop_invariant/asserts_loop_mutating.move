module 0x42::asserts_loop_mutating;

use prover::prover::{ensures, asserts, invariant, clone};

// Body mutates a single counter via `&mut`, decrementing by 1.
// Function-level asserts(`*x >= n`) covers the underflow path.
// Invariant ties the current value of `*x` to the initial value.

fun decrement_ref(x: &mut u64, n: u64) {
    let old_x = clone!(x);
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures((*x as u128) + (i as u128) == (*old_x as u128));
    });
    while (i < n) {
        *x = *x - 1;
        i = i + 1;
    };
}

#[spec(prove)]
fun decrement_ref_spec(x: &mut u64, n: u64) {
    asserts(*x >= n);
    let old_x = clone!(x);
    decrement_ref(x, n);
    ensures((*x as u128) + (n as u128) == (*old_x as u128));
}
