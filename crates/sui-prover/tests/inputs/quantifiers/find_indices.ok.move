#[allow(unused)]
module 0x42::quantifiers_find_indices_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{find_indices, find_indices_range};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_even(x: &u64): bool {
    *x % 2 == 0
}

// Test that all indices in result are valid (within bounds of source)
#[spec(prove)]
fun test_find_indices_valid_indices() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    let len = vector::length(&indices);
    let mut i = 0;

    while (i < len) {
        let idx = *vector::borrow(&indices, i);
        ensures(idx < vector::length(&v));
        i = i + 1;
    };
}

// Test that result length is bounded by source length
#[spec(prove)]
fun test_find_indices_length_bounded() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    ensures(vector::length(&indices) <= vector::length(&v));
}

// Test that indices are sorted (using simple two-element comparison)
#[spec(prove)]
fun test_find_indices_sorted_simple() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    let len = vector::length(&indices);
    if (len >= 2) {
        ensures(*vector::borrow(&indices, 0) < *vector::borrow(&indices, 1));
    };
    if (len >= 3) {
        ensures(*vector::borrow(&indices, 1) < *vector::borrow(&indices, 2));
    };
}

// Test find_indices_range length is bounded by range size
#[spec(prove)]
fun test_find_indices_range_length_bounded() {
    let v = vector[10, 20, 10, 30, 10, 40];
    let result = find_indices_range!<u64>(&v, 1, 4, |x| x_is_10(x));
    
    // Result length bounded by range size (4 - 1 = 3)
    ensures(vector::length(&result) <= 3);
}

// Test that range indices are within the specified range
#[spec(prove)]
fun test_find_indices_range_valid_indices() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices_range!<u64>(&v, 1, 4, |x| x_is_10(x));
    
    let len = vector::length(&indices);
    let mut i = 0;
    
    let idx = *vector::borrow(&indices, 0);
    ensures(idx >= 1);
    ensures(idx < 4);
}

