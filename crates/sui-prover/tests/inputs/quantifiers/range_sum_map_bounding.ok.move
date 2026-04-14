// Tests the bounding axiom for range_sum_map:
//   range_sum_map(a, b) <= range_sum_map(0, n)
// when [a, b] is nested in [0, n]. Relies on the gate that emits bounding
// only when FN's Move return type is a fixed-width unsigned int (here u64).
// Symbolic bounds force the axiom to fire.

#[allow(unused)]
module 0x42::quantifiers_range_sum_map_bounding_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::range_sum_map;

#[ext(pure)]
fun identity(x: u64): u64 {
    x
}

#[spec(prove)]
fun test_range_sum_map_bounding_nested(n: u64, a: u64, b: u64) {
    requires(a <= b && b <= n);
    ensures(
        range_sum_map!<u64>(a, b, |x| identity(x))
            .lte(range_sum_map!<u64>(0, n, |x| identity(x)))
    );
}
