#[allow(unused)]
module 0x42::pool_multi_ok;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun both_positive(x: &u64, y: &u64): bool {
    *x > 0 && *y > 0
}

/// This test uses multiple add_quantifier_pool calls to add terms to the pool.
#[spec(prove)]
fun test_pool_multi_spec() {
    add_quantifier_pool(b"both_positive", 0u64);
    let result = forall!<u64>(|x| both_positive(x, &1));
    ensures(!result);
}
