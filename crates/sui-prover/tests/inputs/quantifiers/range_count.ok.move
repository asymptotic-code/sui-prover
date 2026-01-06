#[allow(unused)]
module 0x42::quantifiers_range_count_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_count;

#[ext(pure)]
fun is_even(x: u64): bool {
    x % 2 == 0
}

#[ext(pure)]
fun is_greater_than_5(x: u64): bool {
    x > 5
}

#[ext(pure)]
fun is_10(x: u64): bool {
    x == 10
}

#[spec(prove)]
fun test_range_count() {
    // Count even numbers in range [0, 4) = {0, 1, 2, 3} -> evens: 0, 2 = 2
    ensures(range_count!(0, 4, |x| is_even(x)) == 2u64.to_int());

    // Count even numbers in range [1, 5) = {1, 2, 3, 4} -> evens: 2, 4 = 2
    ensures(range_count!(1, 5, |x| is_even(x)) == 2u64.to_int());

    // Count numbers > 5 in range [0, 10) = {0..9} -> {6, 7, 8, 9} = 4
    ensures(range_count!(0, 10, |x| is_greater_than_5(x)) == 4u64.to_int());

    // Count numbers > 5 in range [0, 5) = {0..4} -> none = 0
    ensures(range_count!(0, 5, |x| is_greater_than_5(x)) == 0u64.to_int());

    // Empty range should return 0
    ensures(range_count!(0, 0, |x| is_even(x)) == 0u64.to_int());

    // Range where end <= start should return 0
    ensures(range_count!(5, 3, |x| is_even(x)) == 0u64.to_int());
}

#[spec(prove)]
fun test_range_count_specific_value() {
    // Count occurrences of 10 in range [0, 15) -> exactly 1
    ensures(range_count!(0, 15, |x| is_10(x)) == 1u64.to_int());

    // Count occurrences of 10 in range [0, 10) -> 0 (10 is not included)
    ensures(range_count!(0, 10, |x| is_10(x)) == 0u64.to_int());

    // Count occurrences of 10 in range [10, 11) -> exactly 1
    ensures(range_count!(10, 11, |x| is_10(x)) == 1u64.to_int());

    // Count occurrences of 10 in range [11, 20) -> 0
    ensures(range_count!(11, 20, |x| is_10(x)) == 0u64.to_int());
}
