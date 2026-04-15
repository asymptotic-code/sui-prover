#[allow(unused)]
module 0x42::quantifiers_range_sum_map_pure_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_sum_map;

#[spec_only]
use std::integer::Integer;

#[ext(pure)]
fun identity(x: u64): u64 {
    x
}

#[ext(pure)]
fun sum_identity_in_range(start: u64, end: u64): Integer {
    range_sum_map!<u64>(start, end, |x| identity(x))
}

#[spec(prove, extra_bpl = b"range_sum_map_pure.ok.bpl")]
fun test_range_sum_map_pure() {
    // Sum of i for i in [0, 4) = 0 + 1 + 2 + 3 = 6
    ensures(sum_identity_in_range(0, 4) == 6u64.to_int());
}
