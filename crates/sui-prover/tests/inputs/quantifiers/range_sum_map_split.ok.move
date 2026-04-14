// Tests the split axiom for range_sum_map:
//   range_sum_map(0, k) + range_sum_map(k, n) == range_sum_map(0, n)
// Symbolic bounds force the axiom to fire rather than concrete unfolding.

#[allow(unused)]
module 0x42::quantifiers_range_sum_map_split_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::range_sum_map;

#[ext(pure)]
fun identity(x: u64): u64 {
    x
}

#[spec(prove)]
fun test_range_sum_map_split(n: u64, k: u64) {
    requires(k <= n);
    ensures(
        range_sum_map!<u64>(0, k, |x| identity(x))
            .add(range_sum_map!<u64>(k, n, |x| identity(x)))
            == range_sum_map!<u64>(0, n, |x| identity(x))
    );
}
