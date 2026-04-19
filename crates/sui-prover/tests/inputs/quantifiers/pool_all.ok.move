/// Pool provides a counterexample for a forall: not all u64 are less than MAX.
/// The pool term MAX_U64 is the counterexample Z3 needs.
#[allow(unused)]
module 0x42::pool_all_ok;

#[spec_only]
use prover::prover::{forall, ensures, add_quantifier_pool};

#[ext(pure)]
fun is_less_than_max(x: &u64): bool {
    *x < std::u64::max_value!()
}

#[spec(prove)]
fun test_not_all_less_than_max() {
    add_quantifier_pool(b"is_less_than_max", std::u64::max_value!());
    let result = forall!<u64>(|x| is_less_than_max(x));
    ensures(!result);
}
