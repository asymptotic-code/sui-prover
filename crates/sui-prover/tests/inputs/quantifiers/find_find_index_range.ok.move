#[allow(unused)]
module 0x42::quantifiers_find_find_index_range_ok;

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
fun test_find_find_index_range() {
    let v = vector[10, 20, 10, 30];

    // FIND_RANGE: Find in subrange [1, 3) - should find the second 10
    let result = find_range!<u64>(&v, 1, 3, |x| x_is_10(x));
    ensures(*option::borrow(result) == 10);

    // FIND_RANGE: Not found in subrange [1, 2)
    let result2 = find_range!<u64>(&v, 1, 2, |x| x_is_10(x));
    ensures(option::is_none(result2));

    // FIND_INDEX_RANGE: Find index in subrange [1, 3) - should return 2
    let idx = find_index_range!<u64>(&v, 1, 3, |x| x_is_10(x));
    ensures(option::is_some(&idx));

    // FIND_INDEX_RANGE: Find 20 in range [1, 2) - should return 1
    let idx2 = find_index_range!<u64>(&v, 1, 2, |x| x_is_20(x));
    ensures(option::is_some(&idx2));
    ensures(*option::borrow(&idx2) == 1);
}

