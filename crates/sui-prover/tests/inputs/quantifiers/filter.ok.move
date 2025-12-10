#[allow(unused)]
module 0x42::quantifiers_filter_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{filter, filter_range};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_even(x: &u64): bool {
    *x % 2 == 0
}

// Simple test: verify that all elements in result satisfy predicate
#[spec(prove)]
fun test_filter_elements_satisfy_predicate() {
    let v = vector[10, 20, 10, 30];
    let tens = filter!<u64>(&v, |x| x_is_10(x));
    
    // The key property: every element in the result is 10
    let len = vector::length(tens);
    ensures(*vector::borrow(tens, 0) == 10);
    ensures(*vector::borrow(tens, 1) == 10);
}

// Test that result length is bounded by source length
#[spec(prove)]
fun test_filter_length_bounded() {
    let v = vector[10, 20, 10, 30, 10];
    let tens = filter!<u64>(&v, |x| x_is_10(x));
    
    ensures(vector::length(tens) <= vector::length(&v));
}

// Test filter with empty source
#[spec(prove)]
fun test_filter_empty_source() {
    let empty: vector<u64> = vector[];
    let result = filter!<u64>(&empty, |x| x_is_10(x));
    
    // Empty source should give empty result
    ensures(vector::length(result) == 0);
}

// Test filter_range length is bounded
#[spec(prove)]
fun test_filter_range_length_bounded() {
    let v = vector[10, 20, 10, 30, 10, 40];
    let result = filter_range!<u64>(&v, 1, 4, |x| x_is_10(x));
    
    // Result length bounded by range size
    ensures(vector::length(result) <= 3);
}

