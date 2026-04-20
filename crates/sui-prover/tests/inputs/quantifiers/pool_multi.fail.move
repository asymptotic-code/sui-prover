/// Same as pool_multi.ok but WITHOUT the pool hint.
/// Z3 cannot find the counterexample x=0 for both_positive(x, &1) on its own.
#[allow(unused)]
module 0x42::pool_multi_fail;

#[spec_only]
use prover::prover::{forall, ensures};

#[ext(pure)]
fun both_positive(x: &u64, y: &u64): bool {
    *x > 0 && *y > 0
}

#[spec(prove)]
fun test_pool_multi_no_pool_spec() {
    let result = forall!<u64>(|x| both_positive(x, &1));
    ensures(!result);
}
