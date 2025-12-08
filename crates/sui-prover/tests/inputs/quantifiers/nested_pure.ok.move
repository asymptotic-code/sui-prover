#[allow(unused)]
module 0x42::nested_pure_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{any, all, any_range, all_range, count, count_range, sum_map, sum_map_range, map, map_range, find_index, find_index_range};

// Simple predicates
#[ext(pure)]
fun is_even(x: &u64): bool {
    *x % 2 == 0
}

#[ext(pure)]
fun double(x: &u64): u64 {
    if (*x > 9_000_000_000) {
        *x
    } else {
        *x * 2
    }
}

// Nested pure functions using quantifiers

#[ext(pure)]
fun vec_has_even(v: &vector<u64>): bool {
    any!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_all_even(v: &vector<u64>): bool {
    all!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_has_even_in_range(v: &vector<u64>, start: u64, end: u64): bool {
    any_range!<u64>(v, start, end, |x| is_even(x))
}

#[ext(pure)]
fun vec_all_even_in_range(v: &vector<u64>, start: u64, end: u64): bool {
    all_range!<u64>(v, start, end, |x| is_even(x))
}

#[ext(pure)]
fun vec_count_even(v: &vector<u64>): u64 {
    count!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_count_even_in_range(v: &vector<u64>, start: u64, end: u64): u64 {
    count_range!<u64>(v, start, end, |x| is_even(x))
}

#[ext(pure)]
fun vec_sum_doubled(v: &vector<u64>): std::integer::Integer {
    sum_map!<u64, u64>(v, |x| double(x))
}

#[ext(pure)]
fun vec_sum_doubled_in_range(v: &vector<u64>, start: u64, end: u64): std::integer::Integer {
    sum_map_range!<u64, u64>(v, start, end, |x| double(x))
}

#[ext(pure)]
fun vec_doubled(v: &vector<u64>): &vector<u64> {
    map!<u64, u64>(v, |x| double(x))
}

#[ext(pure)]
fun vec_doubled_in_range(v: &vector<u64>, start: u64, end: u64): &vector<u64> {
    map_range!<u64, u64>(v, start, end, |x| double(x))
}

#[ext(pure)]
fun vec_find_even_idx(v: &vector<u64>): std::option::Option<u64> {
    find_index!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_find_even_idx_in_range(v: &vector<u64>, start: u64, end: u64): std::option::Option<u64> {
    find_index_range!<u64>(v, start, end, |x| is_even(x))
}

// Test: any
#[spec(prove)]
fun test_any() {
    let v = vector[1, 2, 3];
    ensures(vec_has_even(&v));
}

// Test: all
#[spec(prove)]
fun test_all() {
    let v = vector[2, 4, 6];
    ensures(vec_all_even(&v));
}

// Test: any_range
#[spec(prove)]
fun test_any_range() {
    let v = vector[1, 2, 3];
    ensures(vec_has_even_in_range(&v, 1, 2)); // range [1,2) contains 2
}

// Test: all_range
#[spec(prove)]
fun test_all_range() {
    let v = vector[1, 2, 4, 3];
    ensures(vec_all_even_in_range(&v, 1, 3)); // range [1,3) contains 2,4
}

// Test: count
#[spec(prove)]
fun test_count() {
    let v = vector[1, 2, 3, 4];
    ensures(vec_count_even(&v) == 2);
}

// Test: count_range
#[spec(prove)]
fun test_count_range() {
    let v = vector[1, 2, 3, 4];
    ensures(vec_count_even_in_range(&v, 0, 3) == 1); // range [0,3) has only 2
}

// Test: sum_map
#[spec(prove)]
fun test_sum_map() {
    let v = vector[1, 2, 3];
    ensures(vec_sum_doubled(&v) == 12u64.to_int()); // 2+4+6 = 12
}

// Test: sum_map_range
#[spec(prove)]
fun test_sum_map_range() {
    let v = vector[1, 2, 3];
    ensures(vec_sum_doubled_in_range(&v, 0, 2) == 6u64.to_int()); // 2+4 = 6
}

// Test: map
#[spec(prove)]
fun test_map() {
    let v = vector[1, 2, 3];
    ensures(*vec_doubled(&v) == vector[2, 4, 6]);
}

// Test: map_range
#[spec(prove)]
fun test_map_range() {
    let v = vector[1, 2, 3];
    ensures(*vec_doubled_in_range(&v, 0, 2) == vector[2, 4]);
}

// Test: find_index
#[spec(prove)]
fun test_find_index() {
    let v = vector[1, 2, 3];
    ensures(vec_find_even_idx(&v) == std::option::some(1)); // index 1 has 2
}

// Test: find_index_range
#[spec(prove)]
fun test_find_index_range() {
    let v = vector[1, 3, 4, 5];
    ensures(vec_find_even_idx_in_range(&v, 1, 4) == std::option::some(2)); // index 2 has 4
}

