/// Pool with the right counterexample value (0) but WRONG name. The pool
/// name "wrong_name" doesn't match "is_positive", so no {:pool} is attached
/// to the quantifier and it's NOT dropped. However, the add_to_pool assume
/// leaks the term 0 into the e-graph. To prevent this from accidentally
/// helping Z3, we use a term (42) that SATISFIES the predicate — even if
/// leaked, it can't serve as a counterexample.
#[allow(unused)]
module 0x42::pool_wrong_name_fail;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[spec(prove)]
fun test_wrong_pool_name() {
    add_quantifier_pool(b"wrong_name", 42u64);
    let result = forall!<u64>(|x| is_positive(x));
    ensures(!result);
}
