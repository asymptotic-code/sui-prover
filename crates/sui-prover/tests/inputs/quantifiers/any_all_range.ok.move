#[allow(unused)]
module 0x42::quantifiers_any_all_range_ok;

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
fun test_any_all_range() {
    let v = vector[10, 20, 10, 30];

    // ANY: Test in subrange [1, 3) - contains [20, 10]
    ensures(any_range!<u64>(&v, 1, 3, |x| x_is_10(x)));           // true: has 10
    ensures(!any_range!<u64>(&v, 1, 2, |x| x_is_10(x)));          // false: only has 20

    // ANY: Empty range should return false
    ensures(!any_range!<u64>(&v, 0, 0, |x| x_is_10(x)));

    // ALL: Test in subrange - all elements positive
    ensures(all_range!<u64>(&v, 1, 3, |x| x_is_positive(x)));     // true: all positive
    ensures(!all_range!<u64>(&v, 1, 3, |x| x_is_greater_than_15(x))); // false: 10 is not > 15

    // ALL: Empty range is vacuously true
    ensures(all_range!<u64>(&v, 0, 0, |x| x_is_greater_than_15(x)));
}
