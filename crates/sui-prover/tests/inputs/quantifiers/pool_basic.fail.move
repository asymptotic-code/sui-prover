/// Same as pool_basic.ok but WITHOUT the pool hint.
/// Z3 cannot find a counterexample to disprove forall(x, x > 10) on its own.
#[allow(unused)]
module 0x42::pool_basic_fail;

#[spec_only]
use prover::prover::{forall, ensures};

#[ext(pure)]
fun gt_10(x: &u64): bool {
    *x > 10
}

#[spec(prove)]
fun test_not_all_gt_10_no_pool() {
    let result = forall!<u64>(|x| gt_10(x));
    ensures(!result);
}
