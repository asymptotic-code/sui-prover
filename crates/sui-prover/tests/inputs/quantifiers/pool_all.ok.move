#[allow(unused)]
module 0x42::pool_all_ok;

#[spec_only]
use prover::prover::{ensures, add_quantifier_pool};

#[spec_only]
use prover::vector_iter::all;

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[spec(prove)]
fun test_pool_all_spec() {
    let v = vector[10, 20, 30];
    let result = all!<u64>(&v, |x| is_positive(x));
    add_quantifier_pool(b"is_positive", 42u64);
    ensures(result);
}
