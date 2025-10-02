module 0x42::foo;

use prover::prover::ensures;
use prover::vec::{slice, sum};

#[spec(prove)]
fun test_slice_and_sum() {
    let v1 = vector[10u64, 20, 30, 40, 50, 60, 70, 80, 90, 100];
    let v2 = vector[5u64, 15, 25, 35, 45];
    
    let slice1 = slice(&v1, 0, 3);  // [10, 20, 30]
    let slice2 = slice(&v1, 3, 7);  // [40, 50, 60, 70]
    let slice3 = slice(&v1, 7, 10); // [80, 90, 100]
    
    let mid_slice = slice(&v1, 2, 8); // [30, 40, 50, 60, 70, 80]
    let mid_sum = sum(mid_slice);
    
    let single = slice(&v1, 5, 6); // [60]
    
    let sum1 = sum(slice1);
    let sum2 = sum(slice2);
    let sum3 = sum(slice3);
    let total_sum = sum(&v1);
    let v2_sum = sum(&v2);
    
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
    
    ensures(sum1 == 60u64.to_int());      // 10 + 20 + 30
    ensures(sum2 == 220u64.to_int());     // 40 + 50 + 60 + 70
    ensures(sum3 == 270u64.to_int());     // 80 + 90 + 100
    ensures(mid_sum == 330u64.to_int());  // 30 + 40 + 50 + 60 + 70 + 80
    ensures(total_sum == 550u64.to_int()); // sum of all elements in v1
    ensures(v2_sum == 125u64.to_int());    // 5 + 15 + 25 + 35 + 45
    
    ensures(sum1.add(sum2).add(sum3) == total_sum);
}
