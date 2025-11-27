#[allow(unused)]
module 0x42::quantifiers_filter_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::filter;

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
    let tens = filter!<u64>(&v, |x| x_is_10(x));
    
    // This assertion is incorrect - should be 2, not 3
    ensures(vector::length(tens) == 3); // EXPECTED FAILURE
}

// This should fail - wrong element value
#[spec(prove)]
fun test_wrong_element() {
    let v = vector[10, 20, 10, 30];
    let tens = filter!<u64>(&v, |x| x_is_10(x));
    
    // All elements should be 10, not 20
    ensures(*vector::borrow(tens, 0) == 20); // EXPECTED FAILURE
}

// This should fail - claiming wrong order
#[spec(prove)]
fun test_wrong_order() {
    let v = vector[10, 20, 30, 40];
    let evens = filter!<u64>(&v, |x| x_is_even(x));
    
    // First element is 10, second is 20, not 30
    ensures(*vector::borrow(evens, 1) == 30); // EXPECTED FAILURE (should be 20)
}

// This should fail - asserting element not in result
#[spec(prove)]
fun test_element_not_matching_predicate() {
    let v = vector[10, 20, 10, 30];
    let tens = filter!<u64>(&v, |x| x_is_10(x));
    
    // 20 and 30 shouldn't be in tens
    ensures(vector::contains(tens, &20)); // EXPECTED FAILURE
}

// This should fail - wrong predicate result assumption
#[spec(prove)]
fun test_wrong_predicate() {
    let v = vector[10, 20, 30, 40];
    let evens = filter!<u64>(&v, |x| x_is_even(x));
    
    // All elements are even, so length should be 4, not 2
    ensures(vector::length(evens) == 2); // EXPECTED FAILURE
}


