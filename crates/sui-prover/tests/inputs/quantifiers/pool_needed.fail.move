#[allow(unused)]
module 0x42::pool_needed_fail;

#[spec_only]
use prover::prover::{forall, ensures};

#[ext(pure)]
fun is_positive(x: &u64): bool {
    *x > 0
}

/// This test does NOT use add_quantifier_pool, so the solver cannot instantiate the quantifier.
/// Without pool hints providing the counterexample (0), verification should fail.
#[spec(prove)]
fun test_pool_needed_spec() {
    let result = forall!<u64>(|x| is_positive(x));
    ensures(!result);
}
