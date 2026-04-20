#[allow(unused)]
module 0x42::pool_needed_ok;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

/// This test uses add_quantifier_pool so the solver can instantiate the quantifier.
#[spec(prove)]
fun test_pool_needed_spec() {
    let result = forall!<u64>(|x| is_positive(x));
    add_quantifier_pool(b"is_positive", 0u64);
    ensures(!result);
}
