module 0x42::loop_invariant_external_bool_with_ensures_fail;

use prover::prover::ensures;

#[spec_only(loop_inv(target = test_spec))]
#[ext(no_abort)]
fun loop_inv(i: u64, n: u64): bool {
    ensures(i <= n);
    i <= n
}

#[spec(prove)]
fun test_spec(n: u64) {
    let mut i = 0;

    while (i < n) {
        i = i + 1;
    };

    ensures(i == n);
}
