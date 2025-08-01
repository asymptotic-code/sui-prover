module 0x42::vector_take_test;

use prover::prover::ensures;

public fun test_take_basic(v: vector<u64>, n: u64): vector<u64> {
    vector::take(v, n)
}

public fun test_take_empty(): vector<u64> {
    let v = vector::empty<u64>();
    vector::take(v, 0)
}

public fun test_take_full(v: vector<u64>): vector<u64> {
    let len = vector::length(&v);
    vector::take(v, len)
}

#[spec(prove)]
fun test_take_zero_spec() {
    let v = vector[0, 1, 2];
    let result = test_take_basic(v, 0);
    ensures(vector::length(&result) == 0);
}

#[spec(prove)]
fun test_take_one_spec() {
    let v = vector[0, 1, 2];
    let result = test_take_basic(v, 1);
    ensures(vector::length(&result) == 1);
    ensures(*vector::borrow(&result, 0) == 0);
}

#[spec(prove)]
fun test_take_two_spec() {
    let v = vector[0, 1, 2];
    let result = test_take_basic(v, 2);
    ensures(vector::length(&result) == 2);
    ensures(*vector::borrow(&result, 0) == 0);
    ensures(*vector::borrow(&result, 1) == 1);
}

#[spec(prove)]
fun test_take_full_spec(v: vector<u64>): vector<u64> {
    let result = test_take_full(v);
    ensures(vector::length(&result) == vector::length(&v));
    result
}

#[spec(prove)]
fun test_take_empty_spec(): vector<u64> {
    let result = test_take_empty();
    ensures(vector::length(&result) == 0);
    result
}

#[spec(prove)]
fun test_take_preserves_elements_spec() {
    let v = vector[10, 20, 30, 40, 50];
    let result = test_take_basic(v, 3);
    
    ensures(vector::length(&result) == 3);
    ensures(*vector::borrow(&result, 0) == 10);
    ensures(*vector::borrow(&result, 1) == 20);
    ensures(*vector::borrow(&result, 2) == 30);
}
