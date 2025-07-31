module 0x42::vector_skip_test;

use prover::prover::ensures;

public fun test_skip_basic(v: vector<u64>, n: u64): vector<u64> {
    vector::skip(v, n)
}

public fun test_skip_all(v: vector<u64>): vector<u64> {
    let len = vector::length(&v);
    vector::skip(v, len)
}

public fun test_skip_empty(): vector<u64> {
    let v = vector::empty<u64>();
    vector::skip(v, 0)
}

#[spec(prove)]
fun test_skip_zero_spec() {
    let v = vector[0, 1, 2];
    let result = test_skip_basic(v, 0);
    ensures(vector::length(&result) == 3);
    ensures(*vector::borrow(&result, 0) == 0);
    ensures(*vector::borrow(&result, 1) == 1);
    ensures(*vector::borrow(&result, 2) == 2);
}

#[spec(prove)]
fun test_skip_one_spec() {
    let v = vector[0, 1, 2];
    let result = test_skip_basic(v, 1);
    ensures(vector::length(&result) == 2);
    ensures(*vector::borrow(&result, 0) == 1);
    ensures(*vector::borrow(&result, 1) == 2);
}

#[spec(prove)]
fun test_skip_two_spec() {
    let v = vector[0, 1, 2];
    let result = test_skip_basic(v, 2);
    ensures(vector::length(&result) == 1);
    ensures(*vector::borrow(&result, 0) == 2);
}

#[spec(prove)]
fun test_skip_all_spec(v: vector<u64>): vector<u64> {
    let result = test_skip_all(v);
    ensures(vector::length(&result) == 0);
    result
}

#[spec(prove)]
fun test_skip_empty_spec(): vector<u64> {
    let result = test_skip_empty();
    ensures(vector::length(&result) == 0);
    result
}

#[spec(prove)]
fun test_skip_preserves_elements_spec() {
    let v = vector[10, 20, 30, 40, 50];
    let result = test_skip_basic(v, 2);
    
    ensures(vector::length(&result) == 3);
    ensures(*vector::borrow(&result, 0) == 30);
    ensures(*vector::borrow(&result, 1) == 40);
    ensures(*vector::borrow(&result, 2) == 50);
}
