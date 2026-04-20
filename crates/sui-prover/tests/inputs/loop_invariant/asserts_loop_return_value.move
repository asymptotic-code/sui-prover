module 0x42::asserts_loop_return_value;

use prover::prover::{ensures, asserts, invariant};

// The function-level asserts both protects against abort and pins down
// a property of the return value. The loop sums `2*1 + 2*2 + ... + 2*n`
// = `n*(n+1)`. The spec's `ensures` on the result is exact.

fun double_and_sum(n: u64): u64 {
    let mut sum: u64 = 0;
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 1000);
        ensures((sum as u128) == (i as u128) * ((i as u128) + 1));
    });
    while (i < n) {
        assert!(i < 1000);
        i = i + 1;
        sum = sum + 2 * i;
    };
    sum
}

#[spec(prove)]
fun double_and_sum_spec(n: u64): u64 {
    asserts(n <= 1000);
    let result = double_and_sum(n);
    ensures((result as u128) == (n as u128) * ((n as u128) + 1));
    result
}
