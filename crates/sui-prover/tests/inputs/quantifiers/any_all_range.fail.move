#[allow(unused)]
module 0x42::quantifiers_any_all_range_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{any_range, all_range};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_positive(x: &u64): bool {
    *x > 0
}

#[ext(pure)]
fun x_is_greater_than_15(x: &u64): bool {
    *x > 15
}

#[spec(prove)]
fun test_any_range_wrong() {
    let v = vector[10, 20, 10, 30];

    // Should fail: 10 exists in full vector but not in range [1, 2)
    // Range [1, 2) only contains [20]
    ensures(any_range!<u64>(&v, 1, 2, |x| x_is_10(x))); // FAIL: should be false
}

#[spec(prove)]
fun test_all_range_wrong() {
    let v = vector[10, 20, 10, 30];

    // Should fail: not all elements in range [1, 3) are > 15
    // Range [1, 3) contains [20, 10], and 10 is not > 15
    ensures(all_range!<u64>(&v, 1, 3, |x| x_is_greater_than_15(x))); // FAIL: should be false
}
