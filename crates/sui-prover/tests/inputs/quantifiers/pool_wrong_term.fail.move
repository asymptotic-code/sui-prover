/// Pool with the WRONG term. We want to prove !forall(x, x > 0), which is
/// true (x=0 is a counterexample). But the pool provides 42 — a value where
/// the predicate HOLDS. Since Boogie drops the quantifier and replaces it
/// with the ground instance P(42) = true, the forall "appears" true and
/// !forall fails.
#[allow(unused)]
module 0x42::pool_wrong_term_fail;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[spec(prove)]
fun test_wrong_pool_term() {
    add_quantifier_pool(b"is_positive", 42u64);
    let result = forall!<u64>(|x| is_positive(x));
    ensures(!result);
}
