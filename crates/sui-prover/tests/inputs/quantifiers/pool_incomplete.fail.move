/// Pool with INCOMPLETE coverage. We want to prove that both
/// !forall(x, x > 0) AND !forall(x, x < MAX) hold. The pool only
/// provides 0 (which disproves x > 0 but satisfies x < MAX). Since
/// the quantifier for x < MAX is replaced with P(0) = true, the
/// second !forall fails.
#[allow(unused)]
module 0x42::pool_incomplete_fail;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

#[ext(pure)]
fun is_less_than_max(x: &u64): bool {
    *x < std::u64::max_value!()
}

#[spec(prove)]
fun test_incomplete_pool() {
    add_quantifier_pool(b"is_positive", 0u64);
    add_quantifier_pool(b"is_less_than_max", 0u64);
    let not_all_positive = !forall!<u64>(|x| is_positive(x));
    let not_all_less = !forall!<u64>(|x| is_less_than_max(x));
    ensures(not_all_positive && not_all_less);
}
