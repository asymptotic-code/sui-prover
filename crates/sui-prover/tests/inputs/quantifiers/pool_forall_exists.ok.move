/// Pool with both forall and exists quantifiers in the same spec.
/// The pool provides counterexample 0 for forall and witness 100 for exists.
#[allow(unused)]
module 0x42::pool_forall_exists_ok;

#[spec_only]
use prover::prover::{forall, exists, ensures, add_quantifier_pool};

#[ext(pure)]
fun gt_50(x: &u64): bool {
    *x > 50
}

#[spec(prove)]
fun test_forall_and_exists() {
    add_quantifier_pool(b"gt_50", 0u64);
    add_quantifier_pool(b"gt_50", 100u64);
    let not_all = !forall!<u64>(|x| gt_50(x));
    let some_exist = exists!<u64>(|x| gt_50(x));
    ensures(not_all && some_exist);
}
