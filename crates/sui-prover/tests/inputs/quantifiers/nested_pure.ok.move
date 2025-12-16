#[allow(unused)]
module 0x42::nested_pure_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{any, all, any_range, all_range, count, count_range, sum_map, sum_map_range, map, map_range, find_index, find_index_range, find, find_range, filter, filter_range, find_indices, find_indices_range};

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

#[ext(pure)]
fun vec_find_even(v: &vector<u64>): std::option::Option<u64> {
    *find!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_find_even_in_range(v: &vector<u64>, start: u64, end: u64): std::option::Option<u64> {
    *find_range!<u64>(v, start, end, |x| is_even(x))
}

#[ext(pure)]
fun vec_filter_even(v: &vector<u64>): &vector<u64> {
    filter!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_filter_even_in_range(v: &vector<u64>, start: u64, end: u64): &vector<u64> {
    filter_range!<u64>(v, start, end, |x| is_even(x))
}

#[ext(pure)]
fun vec_find_even_indices(v: &vector<u64>): vector<u64> {
    find_indices!<u64>(v, |x| is_even(x))
}

#[ext(pure)]
fun vec_find_even_indices_in_range(v: &vector<u64>, start: u64, end: u64): vector<u64> {
    find_indices_range!<u64>(v, start, end, |x| is_even(x))
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
    let mut v = vector[1, 2, 3];

    *vector::borrow_mut(&mut v, 0) = 10u64;
    *vector::borrow_mut(&mut v, 1) = 20u64;
    *vector::borrow_mut(&mut v, 2) = 30u64;

    ensures(vec_sum_doubled(&v) == 120u64.to_int()); // 20+40+60 = 120
}

// Test: sum_map_range
#[spec(prove)]
fun test_sum_map_range() {
    let mut v = vector[1, 2, 3];

    *vector::borrow_mut(&mut v, 0) = 10u64;
    *vector::borrow_mut(&mut v, 1) = 20u64;
    *vector::borrow_mut(&mut v, 2) = 30u64;

    ensures(vec_sum_doubled_in_range(&v, 0, 2) == 60u64.to_int()); // 20+40 = 60
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

// Test: find
#[spec(prove)]
fun test_find() {
    let v = vector[1, 2, 3];
    ensures(vec_find_even(&v) == std::option::some(2)); // finds element 2
}

// Test: find_range
#[spec(prove)]
fun test_find_range() {
    let v = vector[1, 3, 4, 5];
    ensures(vec_find_even_in_range(&v, 1, 4) == std::option::some(4)); // finds element 4 in range [1,4)
}

// Test: filter
#[spec(prove)]
fun test_filter() {
    let v = vector[1, 2, 3, 4];
    ensures(*vec_filter_even(&v) == vector[2, 4]); // filters to only even elements
}

// Test: filter_range
#[spec(prove)]
fun test_filter_range() {
    let v = vector[1, 2, 3, 4];
    ensures(*vec_filter_even_in_range(&v, 1, 4) == vector[2, 4]); // filters range [1,4) to even elements
}

// Test: find_indices
#[spec(prove)]
fun test_find_indices() {
    let v = vector[10, 20, 30, 40];
    ensures(vec_find_even_indices(&v) == vector[1, 3]); // indices 1 and 3 have even elements (20, 40)
}

// Test: find_indices_range
#[spec(prove)]
fun test_find_indices_range() {
    let v = vector[10, 20, 30, 40];
    ensures(vec_find_even_indices_in_range(&v, 0, 2) == vector[1]); // index 1 has 20
}
