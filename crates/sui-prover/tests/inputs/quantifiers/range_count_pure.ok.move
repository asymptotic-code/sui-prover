#[allow(unused)]
module 0x42::quantifiers_range_count_pure_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_count;

#[spec_only]
use std::integer::Integer;

#[ext(pure)]
fun is_even(x: u64): bool {
    x % 2 == 0
}

#[ext(pure)]
fun count_evens_in_range(start: u64, end: u64): Integer {
    range_count!(start, end, |x| is_even(x))
}

#[spec(prove)]
fun test_range_count_pure() {
    // Count even numbers in [0, 6) = {0, 2, 4} = 3
    ensures(count_evens_in_range(0, 6) == 3u64.to_int());
}

