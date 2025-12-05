#[allow(unused)]
module 0x42::quantifiers_count_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_positive(x: &u64): bool {
    *x > 0
}

#[ext(pure)]
fun x_is_greater_than_100(x: &u64): bool {
    *x > 100
}

#[spec(prove)]
fun test_count() {
    let v = vector[10, 20, 10, 30];

    // Test COUNT
    ensures(count!<u64>(&v, |x| x_is_10(x)) == 2);
    ensures(count!<u64>(&v, |x| x_is_positive(x)) == 4);
    ensures(count!<u64>(&v, |x| x_is_greater_than_100(x)) == 0);

    // Test COUNT_RANGE
    ensures(count_range!<u64>(&v, 0, 4, |x| x_is_10(x)) == 2);
    ensures(count_range!<u64>(&v, 0, 2, |x| x_is_10(x)) == 1); // First 10 is at index 0
    ensures(count_range!<u64>(&v, 1, 4, |x| x_is_10(x)) == 1); // Second 10 is at index 2
    ensures(count_range!<u64>(&v, 1, 2, |x| x_is_10(x)) == 0); // Range [1, 2) is just [20], so no 10s
}

