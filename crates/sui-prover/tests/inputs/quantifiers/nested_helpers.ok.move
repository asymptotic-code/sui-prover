// Compose two iterator helpers in a single expression to stress the
// interaction between their axioms. e.g. `count(filter(v, p), q)` creates a
// term where both the Filter and Count axioms must fire together.

#[allow(unused)]
module 0x42::quantifiers_nested_helpers_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{count, filter, map, sum_map, find_index};

#[ext(pure)]
fun is_even(x: &u64): bool {
    *x % 2 == 0
}

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[ext(pure)]
fun double(x: &u64): u64 {
    if (*x > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        *x * 2
    }
}

// count over a filtered vector.
#[spec(prove)]
fun test_count_of_filter() {
    let v = vector[0, 1, 2, 3, 4, 5];
    // Filter to evens [0, 2, 4], then count positives [2, 4] -> 2.
    ensures(count!<u64>(filter!<u64>(&v, |x| is_even(x)), |x| is_positive(x)) == 2);
}

// sum_map over a filtered vector.
#[spec(prove)]
fun test_sum_map_of_filter() {
    let v = vector[1, 2, 3, 4];
    // Filter to evens [2, 4], then double -> [4, 8], sum = 12.
    ensures(sum_map!<u64, u64>(filter!<u64>(&v, |x| is_even(x)), |x| double(x)) == 12u64.to_int());
}

// find_index into a mapped vector.
#[spec(prove)]
fun test_find_index_of_map() {
    let v = vector[1, 2, 3, 4];
    // Map to doubles [2, 4, 6, 8], first even is at index 0.
    ensures(find_index!<u64>(map!<u64, u64>(&v, |x| double(x)), |x| is_even(x)) == option::some(0));
}

// count over a mapped vector.
#[spec(prove)]
fun test_count_of_map() {
    let v = vector[0, 1, 2, 3];
    // Map to doubles [0, 2, 4, 6], count positives -> 3.
    ensures(count!<u64>(map!<u64, u64>(&v, |x| double(x)), |x| is_positive(x)) == 3);
}
