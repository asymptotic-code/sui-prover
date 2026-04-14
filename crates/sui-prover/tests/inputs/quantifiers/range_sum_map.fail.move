#[allow(unused)]
module 0x42::quantifiers_range_sum_map_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_sum_map;

#[ext(pure)]
fun identity(x: u64): u64 {
    x
}

#[spec(prove)]
fun test_range_sum_map_wrong_sum() {
    // Sum of i for i in [0, 4) = 6, not 7
    ensures(range_sum_map!<u64>(0, 4, |x| identity(x)) == 7u64.to_int());
}

#[spec(prove)]
fun test_range_sum_map_empty_not_zero() {
    // Empty range is 0, not 1
    ensures(range_sum_map!<u64>(5, 5, |x| identity(x)) == 1u64.to_int());
}
