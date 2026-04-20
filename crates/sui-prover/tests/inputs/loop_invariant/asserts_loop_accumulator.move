module 0x42::asserts_loop_accumulator;

use prover::prover::{ensures, asserts, invariant};

// Sum 1 + 2 + ... + n into a u64. The function-level asserts bounds n
// so the closed-form sum fits in u64. The invariant carries:
//   * the closed-form equality `sum == i*(i+1)/2`,
//   * the "asserts-up-to-i" bound `i <= MAX_N` (closes Assume).
// An explicit `assert!(i < MAX_N)` in the body propagates the bound in
// the Assume direction, since the implicit overflow check on `sum + i`
// alone does not constrain `i` tightly enough.

const MAX_N: u64 = 1000;

fun bounded_sum(n: u64): u64 {
    let mut sum: u64 = 0;
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= MAX_N);
        ensures((sum as u128) == (i as u128) * ((i as u128) + 1) / 2);
    });
    while (i < n) {
        assert!(i < MAX_N);
        i = i + 1;
        sum = sum + i;
    };
    sum
}

#[spec(prove)]
fun bounded_sum_spec(n: u64): u64 {
    asserts(n <= MAX_N);
    let result = bounded_sum(n);
    ensures((result as u128) == (n as u128) * ((n as u128) + 1) / 2);
    result
}
