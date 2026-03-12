#[allow(unused)]
module 0x42::pool_basic_ok;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[spec(prove)]
fun test_pool_spec() {
    let result = forall!<u64>(|x| is_positive(x));
    add_quantifier_pool(b"is_positive", 42u64);
    ensures(!result || is_positive(&42));
}
