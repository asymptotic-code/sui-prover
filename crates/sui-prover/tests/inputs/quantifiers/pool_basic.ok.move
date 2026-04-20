/// Pool provides a counterexample to disprove a universal: not all u64 are > 10.
/// The pool term 5 is the counterexample Z3 needs.
#[allow(unused)]
module 0x42::pool_basic_ok;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun gt_10(x: &u64): bool {
    *x > 10
}

#[spec(prove)]
fun test_not_all_gt_10() {
    add_quantifier_pool(b"gt_10", 5u64);
    let result = forall!<u64>(|x| gt_10(x));
    ensures(!result);
}
