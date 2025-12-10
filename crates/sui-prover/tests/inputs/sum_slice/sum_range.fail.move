module 0x42::foo;

use prover::prover::ensures;
use prover::vector_iter::sum_range;


#[spec(prove)]
fun test_sum() {
    let v2 = vector[5u64, 15, 25, 35, 45];
    let v2_sum = sum_range(&v2, 1, 3);

    ensures(v2_sum == 50u64.to_int()); // Should fails because sum [1,3) is 40
}
