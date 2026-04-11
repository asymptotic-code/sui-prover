// Stress test: filter on a larger concrete vector.

#[allow(unused)]
module 0x42::quantifiers_filter_big_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::filter;

#[ext(pure)]
fun is_even(x: &u64): bool {
    *x % 2 == 0
}

#[spec(prove)]
fun test_filter_big() {
    let v = vector[1, 2, 3, 4, 5, 6, 7, 8];
    ensures(filter!<u64>(&v, |x| is_even(x)) == vector[2, 4, 6, 8]);
}
