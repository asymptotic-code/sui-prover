// Loop test for range_sum_map: accumulate 0/1 contributions (odd or not)
// and prove the running sum matches range_sum_map over the processed prefix.
// Bounded contributions keep the sum <= i, so no overflow concerns.

module 0x42::range_sum_map_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::range_sum_map;

#[ext(pure)]
fun odd_to_int(x: u64): u64 {
    if (x % 2 == 1) { 1 } else { 0 }
}

fun count_odd_via_range_sum(n: u64): u64 {
    let mut i = 0;
    let mut s: u64 = 0;
    invariant!(|| ensures(
        i <= n
            && s <= i
            && s.to_int() == range_sum_map!<u64>(0, i, |j| odd_to_int(j))
    ));
    while (i < n) {
        s = s + odd_to_int(i);
        i = i + 1;
    };
    s
}

#[spec(prove)]
fun count_odd_via_range_sum_spec(n: u64): u64 {
    let r = count_odd_via_range_sum(n);
    ensures(r.to_int() == range_sum_map!<u64>(0, n, |j| odd_to_int(j)));
    r
}
