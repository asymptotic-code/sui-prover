// Stress test: count on a larger concrete vector, verifying the recursive
// count axiom scales.

#[allow(unused)]
module 0x42::quantifiers_count_big_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::count;

#[ext(pure)]
fun is_even(x: &u64): bool {
    *x % 2 == 0
}

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[spec(prove)]
fun test_count_big() {
    let v = vector[1, 2, 3, 4, 5, 6, 7, 8];
    // 4 evens: 2, 4, 6, 8
    ensures(count!<u64>(&v, |x| is_even(x)) == 4);
    // 8 positives (all of them)
    ensures(count!<u64>(&v, |x| is_positive(x)) == 8);
}
