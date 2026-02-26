module 0x42::loop_invariant_external_void_with_requires_fail;

use prover::prover::{requires, ensures};

#[spec_only(loop_inv(target = test_spec))]
#[ext(no_abort)]
fun loop_inv(i: u64, n: u64) {
    requires(i <= n);
    ensures(i <= n);
}

#[spec(prove)]
fun test_spec(n: u64) {
    let mut i = 0;

    while (i < n) {
        i = i + 1;
    };

    ensures(i == n);
}
