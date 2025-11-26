#[allow(unused)]
module 0x42::quantifiers_count_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[spec(prove)]
fun test_count_fail() {
    let v = vector[10, 20, 10, 30];

    // This should fail because count is 2
    ensures(count!<u64>(&v, |x| x_is_10(x)) == 3);
}

#[spec(prove)]
fun test_count_range_fail() {
    let v = vector[10, 20, 10, 30];

    // This should fail because range [0, 2) has one 10, so count is 1
    ensures(count_range!<u64>(&v, 0, 2, |x| x_is_10(x)) == 2);
}

