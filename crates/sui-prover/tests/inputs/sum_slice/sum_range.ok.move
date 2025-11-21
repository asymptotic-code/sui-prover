module 0x42::foo;

use prover::prover::{requires, ensures};
use prover::vector_iter::sum_range;


#[spec(prove)]
fun test_sum(mut v: vector<u64>) {
    let mut v1 = vector[10u64, 20, 30];
    let mut v2 = vector[5u64, 15, 1, 1];
    requires(vector::length(&v) == 2);

    // Use borrow_mut to modify vector elements
    *vector::borrow_mut(&mut v1, 0) = 100u64;
    *vector::borrow_mut(&mut v1, 1) = 200u64;
    *vector::borrow_mut(&mut v1, 2) = 400u64;

    *vector::borrow_mut(&mut v2, 0) = 5u64;
    *vector::borrow_mut(&mut v2, 1) = 15u64;
    *vector::borrow_mut(&mut v2, 2) = 25u64;
    *vector::borrow_mut(&mut v2, 3) = 35u64;

    *vector::borrow_mut(&mut v, 0) = 50u64;
    *vector::borrow_mut(&mut v, 1) = 75u64;

    let v1_sum = sum_range(&v1, 1, 3);
    let v2_sum = sum_range(&v2, 0, 1);
    let v3_sum = sum_range(&v2, 1, 4);
    let v_sum = sum_range(&v, 0, vector::length(&v));
    
    ensures(v1_sum == 600u64.to_int());
    ensures(v2_sum == 5u64.to_int());
    ensures(v3_sum == 75u64.to_int());
    ensures(v_sum == 125u64.to_int());
}
