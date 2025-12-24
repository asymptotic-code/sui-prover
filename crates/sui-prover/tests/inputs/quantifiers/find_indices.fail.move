#[allow(unused)]
module 0x42::quantifiers_find_indices_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::find_indices;

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_even(x: &u64): bool {
    *x % 2 == 0
}

// This should fail - wrong count
#[spec(prove)]
fun test_wrong_count() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    // This assertion is incorrect - should be 2, not 3
    ensures(vector::length(&indices) == 3); // EXPECTED FAILURE 1
}

// This should fail - wrong index value
#[spec(prove)]
fun test_wrong_index() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    // First occurrence is at index 0, not 1
    ensures(*vector::borrow(&indices, 0) == 1); // EXPECTED FAILURE 2
}

// This should fail - claiming a non-existent index
#[spec(prove)]
fun test_wrong_contains() {
    let v = vector[10, 20, 10, 30];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    // Index 1 has value 20, not 10, so 1 shouldn't be in indices
    ensures(vector::contains(&indices, &1)); // EXPECTED FAILURE 3
}

// This should fail - assuming wrong order
#[spec(prove)]
fun test_wrong_order() {
    let v = vector[10, 20, 10, 30, 10];
    let indices = find_indices!<u64>(&v, |x| x_is_10(x));
    
    // Indices should be 0, 2, 4 - not 0, 4, 2
    ensures(*vector::borrow(&indices, 1) == 4); // EXPECTED FAILURE 4
}

// This should fail - wrong predicate count assumption
#[spec(prove)]
fun test_wrong_predicate() {
    let v = vector[10, 20, 30, 40];
    let indices = find_indices!<u64>(&v, |x| x_is_even(x));
    
    // All elements are even, so length should be 4, not 2
    ensures(vector::length(&indices) == 2); // EXPECTED FAILURE 5
}
