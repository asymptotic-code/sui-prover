module 0x42::foo;

use prover::prover::ensures;
use prover::vector_iter::sum;


#[spec(prove)]
fun test_sum() {
    let v1 = vector[10u64, 20, 30, 40, 50, 60, 70, 80, 90, 100];
    let v2 = vector[5u64, 15, 25, 35, 45];
    let v3: vector<u64> = vector[]; // empty vector

    let v1_sum = sum(&v1);
    let v2_sum = sum(&v2);
    let v3_sum = sum(&v3);
    
    ensures(v1_sum == 550u64.to_int()); // sum of all elements in v1
    ensures(v2_sum == 125u64.to_int());    // 5 + 15 + 25 + 35 + 45    
    ensures(v3_sum == 0u64.to_int());   // sum of empty vector is 0
}
