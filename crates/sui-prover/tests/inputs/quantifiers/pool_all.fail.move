/// Same as pool_all.ok but WITHOUT the pool hint.
/// Z3 cannot find the counterexample MAX_U64 on its own.
#[allow(unused)]
module 0x42::pool_all_fail;

#[spec_only]
use prover::prover::{forall, ensures};

#[ext(pure)]
fun is_less_than_max(x: &u64): bool {
    *x < std::u64::max_value!()
}

#[spec(prove)]
fun test_not_all_less_than_max_no_pool() {
    let result = forall!<u64>(|x| is_less_than_max(x));
    ensures(!result);
}
