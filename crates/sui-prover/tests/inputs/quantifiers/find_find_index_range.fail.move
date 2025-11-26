#[allow(unused)]
module 0x42::quantifiers_find_find_index_range_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{find_range, find_index_range};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_20(x: &u64): bool {
    *x == 20
}

#[spec(prove)]
fun test_find_range_wrong_value() {
    let v = vector[10, 20, 10, 30];

    // Should fail: find returns 10, not 20
    let result = find_range!<u64>(&v, 0, 4, |x| x_is_10(x));
    ensures(option::is_none(result)); // FAIL: should be some
}

#[spec(prove)]
fun test_find_index_range_wrong_index() {
    let v = vector[10, 20, 10, 30];

    // Should fail: 10 in range [1, 3) is at index 2, not 0
    let idx = find_index_range!<u64>(&v, 1, 3, |x| x_is_10(x));
    ensures(option::is_some(&idx));
    ensures(*option::borrow(&idx) == 0); // FAIL: should be 2
}

