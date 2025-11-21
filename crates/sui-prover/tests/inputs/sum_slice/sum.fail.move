module 0x42::foo;

use prover::prover::ensures;
use prover::vector_iter::sum;


#[spec(prove)]
fun test_sum() {
    let v2 = vector[5u64, 15, 25, 35, 45];
    let v2_sum = sum(&v2);

    ensures(v2_sum == 55u64.to_int());  
}
