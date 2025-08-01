module 0x42::vector_take_skip_combined_test;

use prover::prover::ensures;

public fun test_take_basic(v: vector<u64>, n: u64): vector<u64> {
    vector::take(v, n)
}

public fun test_skip_basic(v: vector<u64>, n: u64): vector<u64> {
    vector::skip(v, n)
}

#[spec(prove)]
fun test_take_skip_complement_spec() {
    let v = vector[0, 1, 2, 3, 4];
    let n = 2;
    
    // Test take - should get first n elements
    let taken = test_take_basic(v, n);
    ensures(vector::length(&taken) == 2);
    ensures(*vector::borrow(&taken, 0) == 0);
    ensures(*vector::borrow(&taken, 1) == 1);
    
    let v2 = vector[0, 1, 2, 3, 4];
    let skipped = test_skip_basic(v2, n);
    ensures(vector::length(&skipped) == 3);
    ensures(*vector::borrow(&skipped, 0) == 2);
    ensures(*vector::borrow(&skipped, 1) == 3);
    ensures(*vector::borrow(&skipped, 2) == 4);
}

#[spec(prove)]
fun test_take_skip_zero_spec() {
    let v = vector[10, 20, 30];
    
    let taken = test_take_basic(v, 0);
    ensures(vector::length(&taken) == 0);
    
    let v2 = vector[10, 20, 30];
    let skipped = test_skip_basic(v2, 0);
    ensures(vector::length(&skipped) == 3);
    ensures(*vector::borrow(&skipped, 0) == 10);
    ensures(*vector::borrow(&skipped, 1) == 20);
    ensures(*vector::borrow(&skipped, 2) == 30);
}

#[spec(prove)]
fun test_take_skip_full_length_spec() {
    let v = vector[100, 200];
    let len = 2;
    
    let taken = test_take_basic(v, len);
    ensures(vector::length(&taken) == 2);
    ensures(*vector::borrow(&taken, 0) == 100);
    ensures(*vector::borrow(&taken, 1) == 200);
    
    let v2 = vector[100, 200];
    let skipped = test_skip_basic(v2, len);
    ensures(vector::length(&skipped) == 0);
}
