#[allow(unused)]
module 0x42::nested_pure_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{any, all, any_range, all_range, count, count_range, sum_map, sum_map_range, map, map_range, find_index, find_index_range, find, find_range, filter, filter_range, find_indices, find_indices_range};

#[ext(pure)]
fun is_divisible_by(x: &u64, divisor: u64): bool {
    if (divisor == 0) {
        false
    } else {
        *x % divisor == 0
    }
}

#[ext(pure)]
fun is_in_range(x: &u64, min: u64, max: u64): bool {
    *x >= min && *x <= max
}

#[ext(pure)]
fun multiply_by(x: &u64, factor: u64): u64 {
    if (factor == 0) {
        0
    } else {
        if (*x > 9_000_000_000 / factor) {
            *x
        } else {
            *x * factor
        }
    }
}

#[ext(pure)]
fun add_and_multiply(x: &u64, addend: u64, multiplier: u64): u64 {
    if (*x > 18_446_744_073_709_551_615u64 - addend) {
        *x
    } else {
        let sum = *x + addend;
        if (multiplier == 0) {
            0
        } else if (sum > 18_446_744_073_709_551_615u64 / multiplier) {
            *x
        } else {
            sum * multiplier
        }
    }
}

#[ext(pure)]
fun vec_has_divisible(v: &vector<u64>, divisor: u64): bool {
    any!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_all_divisible(v: &vector<u64>, divisor: u64): bool {
    all!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_all_in_range(v: &vector<u64>, min: u64, max: u64): bool {
    all!<u64>(v, |x| is_in_range(x, min, max))
}

#[ext(pure)]
fun vec_has_divisible_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): bool {
    any_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_all_divisible_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): bool {
    all_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_count_divisible(v: &vector<u64>, divisor: u64): u64 {
    count!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_count_divisible_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): u64 {
    count_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_sum_multiplied(v: &vector<u64>, factor: u64): std::integer::Integer {
    sum_map!<u64, u64>(v, |x| multiply_by(x, factor))
}

#[ext(pure)]
fun vec_sum_multiplied_in_range(v: &vector<u64>, start: u64, end: u64, factor: u64): std::integer::Integer {
    sum_map_range!<u64, u64>(v, start, end, |x| multiply_by(x, factor))
}

#[ext(pure)]
fun vec_sum_add_and_multiply(v: &vector<u64>, addend: u64, multiplier: u64): std::integer::Integer {
    sum_map!<u64, u64>(v, |x| add_and_multiply(x, addend, multiplier))
}

#[ext(pure)]
fun vec_multiplied(v: &vector<u64>, factor: u64): &vector<u64> {
    map!<u64, u64>(v, |x| multiply_by(x, factor))
}

#[ext(pure)]
fun vec_multiplied_in_range(v: &vector<u64>, start: u64, end: u64, factor: u64): &vector<u64> {
    map_range!<u64, u64>(v, start, end, |x| multiply_by(x, factor))
}

#[ext(pure)]
fun vec_transform(v: &vector<u64>, addend: u64, multiplier: u64): &vector<u64> {
    map!<u64, u64>(v, |x| add_and_multiply(x, addend, multiplier))
}

#[ext(pure)]
fun vec_find_divisible_idx(v: &vector<u64>, divisor: u64): std::option::Option<u64> {
    find_index!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_find_divisible_idx_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): std::option::Option<u64> {
    find_index_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_find_divisible(v: &vector<u64>, divisor: u64): std::option::Option<u64> {
    *find!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_find_divisible_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): std::option::Option<u64> {
    *find_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_filter_divisible(v: &vector<u64>, divisor: u64): &vector<u64> {
    filter!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_filter_divisible_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): &vector<u64> {
    filter_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_filter_in_range(v: &vector<u64>): &vector<u64> {
    let min = 5;
    let max = 15;
    filter!<u64>(v, |x| is_in_range(x, min, max))
}

#[ext(pure)]
fun vec_find_divisible_indices(v: &vector<u64>, divisor: u64): vector<u64> {
    find_indices!<u64>(v, |x| is_divisible_by(x, divisor))
}

#[ext(pure)]
fun vec_find_divisible_indices_in_range(v: &vector<u64>, start: u64, end: u64, divisor: u64): vector<u64> {
    find_indices_range!<u64>(v, start, end, |x| is_divisible_by(x, divisor))
}

// Test: any with divisor from context
#[spec(prove)]
fun test_any() {
    let v = vector[1, 2, 3];
    let divisor = 2;
    ensures(vec_has_divisible(&v, divisor)); // checks if any element is divisible by 2
}

// Test: all with divisor from context
#[spec(prove)]
fun test_all() {
    let v = vector[2, 4, 6];
    let divisor = 2;
    ensures(vec_all_divisible(&v, divisor)); // checks if all elements are divisible by 2
}

// Test: all with range check using multiple context params
#[spec(prove)]
fun test_all_range_check() {
    let v = vector[5, 7, 9];
    let min = 5;
    let max = 10;
    ensures(vec_all_in_range(&v, min, max)); // checks if all elements are in [5,10]
}

// Test: any_range with divisor from context
#[spec(prove)]
fun test_any_range() {
    let v = vector[1, 2, 3];
    let divisor = 2;
    ensures(vec_has_divisible_in_range(&v, 1, 2, divisor)); // range [1,2) contains 2 which is divisible by 2
}

// Test: all_range with divisor from context
#[spec(prove)]
fun test_all_range() {
    let v = vector[1, 2, 4, 3];
    let divisor = 2;
    ensures(vec_all_divisible_in_range(&v, 1, 3, divisor)); // range [1,3) contains 2,4 both divisible by 2
}

// Test: count with divisor from context
#[spec(prove)]
fun test_count() {
    let v = vector[1, 2, 3, 4];
    let divisor = 2;
    ensures(vec_count_divisible(&v, divisor) == 2); // 2 and 4 are divisible by 2
}

// Test: count_range with divisor from context
#[spec(prove)]
fun test_count_range() {
    let v = vector[1, 2, 3, 4];
    let divisor = 2;
    ensures(vec_count_divisible_in_range(&v, 0, 3, divisor) == 1); // range [0,3) has only 2
}

// Test: sum_map with factor from context
#[spec(prove)]
fun test_sum_map() {
    let mut v = vector[1, 2, 3];

    *vector::borrow_mut(&mut v, 0) = 10u64;
    *vector::borrow_mut(&mut v, 1) = 20u64;
    *vector::borrow_mut(&mut v, 2) = 30u64;

    let factor = 2;
    ensures(vec_sum_multiplied(&v, factor) == 120u64.to_int()); // (10*2)+(20*2)+(30*2) = 120
}

// Test: sum_map_range with factor from context
#[spec(prove)]
fun test_sum_map_range() {
    let mut v = vector[1, 2, 3];

    *vector::borrow_mut(&mut v, 0) = 10u64;
    *vector::borrow_mut(&mut v, 1) = 20u64;
    *vector::borrow_mut(&mut v, 2) = 30u64;

    let factor = 2;
    ensures(vec_sum_multiplied_in_range(&v, 0, 2, factor) == 60u64.to_int()); // (10*2)+(20*2) = 60
}

// Test: sum_map with multiple context parameters
#[spec(prove)]
fun test_sum_map_multi_param() {
    let v = vector[1, 2, 3];
    let addend = 5;
    let multiplier = 3;
    ensures(vec_sum_add_and_multiply(&v, addend, multiplier) == 63u64.to_int()); // (1+5)*3+(2+5)*3+(3+5)*3 = 18+21+24 = 63
}

// Test: map with factor from context
#[spec(prove)]
fun test_map() {
    let v = vector[1, 2, 3];
    let factor = 2;
    ensures(*vec_multiplied(&v, factor) == vector[2, 4, 6]);
}

// Test: map_range with factor from context
#[spec(prove)]
fun test_map_range() {
    let v = vector[1, 2, 3];
    let factor = 2;
    ensures(*vec_multiplied_in_range(&v, 0, 2, factor) == vector[2, 4]);
}

// Test: map with multiple context parameters
#[spec(prove)]
fun test_map_multi_param() {
    let v = vector[1, 2, 3];
    let addend = 10;
    let multiplier = 2;
    ensures(*vec_transform(&v, addend, multiplier) == vector[22, 24, 26]); // (1+10)*2=22, (2+10)*2=24, (3+10)*2=26
}

// Test: find_index with divisor from context
#[spec(prove)]
fun test_find_index() {
    let v = vector[1, 2, 3];
    let divisor = 2;
    ensures(vec_find_divisible_idx(&v, divisor) == std::option::some(1)); // index 1 has 2
}

// Test: find_index_range with divisor from context
#[spec(prove)]
fun test_find_index_range() {
    let v = vector[1, 3, 4, 5];
    let divisor = 2;
    ensures(vec_find_divisible_idx_in_range(&v, 1, 4, divisor) == std::option::some(2)); // index 2 has 4
}

// Test: find with divisor from context
#[spec(prove)]
fun test_find() {
    let v = vector[1, 2, 3];
    let divisor = 2;
    ensures(vec_find_divisible(&v, divisor) == std::option::some(2)); // finds element 2
}

// Test: find_range with divisor from context
#[spec(prove)]
fun test_find_range() {
    let v = vector[1, 3, 4, 5];
    let divisor = 2;
    ensures(vec_find_divisible_in_range(&v, 1, 4, divisor) == std::option::some(4)); // finds element 4 in range [1,4)
}

// Test: filter with divisor from context
#[spec(prove)]
fun test_filter() {
    let v = vector[1, 2, 3, 4];
    let divisor = 2;
    ensures(*vec_filter_divisible(&v, divisor) == vector[2, 4]); // filters to only elements divisible by 2
}

// Test: filter_range with divisor from context
#[spec(prove)]
fun test_filter_range() {
    let v = vector[1, 2, 3, 4];
    let divisor = 2;
    ensures(*vec_filter_divisible_in_range(&v, 1, 4, divisor) == vector[2, 4]); // filters range [1,4) to elements divisible by 2
}

// Test: filter with multiple context parameters
#[spec(prove)]
fun test_filter_range_check() {
    let v = vector[1, 5, 10, 15];
    ensures(*vec_filter_in_range(&v) == vector[5, 10, 15]); // filters to elements in [5,15]
}

// Test: find_indices with divisor from context
#[spec(prove)]
fun test_find_indices() {
    let v = vector[10, 20, 30, 40];
    let divisor = 20;
    ensures(vec_find_divisible_indices(&v, divisor) == vector[1, 3]); // indices 1 and 3 have elements divisible by 20 (20, 40)
}

// Test: find_indices_range with divisor from context
#[spec(prove)]
fun test_find_indices_range() {
    let v = vector[10, 20, 30, 40];
    let divisor = 20;
    ensures(vec_find_divisible_indices_in_range(&v, 0, 2, divisor) == vector[1]); // index 1 has 20
}
