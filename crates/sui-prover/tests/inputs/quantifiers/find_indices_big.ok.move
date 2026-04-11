// Stress test: find_indices on a larger concrete vector.

#[allow(unused)]
module 0x42::quantifiers_find_indices_big_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::find_indices;

#[ext(pure)]
fun is_even(x: &u64): bool {
    *x % 2 == 0
}

#[spec(prove)]
fun test_find_indices_big() {
    let v = vector[1, 2, 3, 4, 5, 6, 7, 8];
    // Even elements are at indices 1, 3, 5, 7.
    ensures(*find_indices!<u64>(&v, |x| is_even(x)) == vector[1, 3, 5, 7]);
}
