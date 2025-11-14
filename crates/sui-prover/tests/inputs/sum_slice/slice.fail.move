module 0x42::slice_fail;

use prover::prover::ensures;
use prover::vector_iter::slice;

#[spec(prove)]
fun test_slice() {
    let v1 = vector[10u64, 20, 30, 40, 50, 60, 70, 80, 90, 100];
    
    let slice1 = slice(&v1, 0, 3);  // [10, 20, 30]
    
    ensures(vector::length(slice1) == 2);
    ensures(*vector::borrow(slice1, 0) == 20);
}
