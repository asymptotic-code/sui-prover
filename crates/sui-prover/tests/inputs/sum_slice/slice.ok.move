module 0x42::slice_ok;

use prover::prover::ensures;
use prover::vector_iter::slice;

#[spec(prove)]
fun test_slice() {
    let v1 = vector[10u64, 20, 30, 40, 50, 60, 70, 80, 90, 100];
    
    let slice1 = slice(&v1, 0, 3);  // [10, 20, 30]
    let slice2 = slice(&v1, 3, 7);  // [40, 50, 60, 70]
    let slice3 = slice(&v1, 7, 10); // [80, 90, 100]
    
    let mid_slice = slice(&v1, 2, 8); // [30, 40, 50, 60, 70, 80]
    
    let single = slice(&v1, 5, 6); // [60]
    
    ensures(vector::length(slice1) == 3);
    ensures(vector::length(slice2) == 4);
    ensures(vector::length(slice3) == 3);
    ensures(vector::length(mid_slice) == 6);
    ensures(vector::length(single) == 1);
    
    ensures(*vector::borrow(slice1, 0) == 10);
    ensures(*vector::borrow(slice1, 2) == 30);
    ensures(*vector::borrow(slice2, 0) == 40);
    ensures(*vector::borrow(slice2, 3) == 70);
    ensures(*vector::borrow(single, 0) == 60);
}
