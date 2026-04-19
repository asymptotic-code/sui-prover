/// Same as pool_forall_exists.ok but without pool hints.
#[allow(unused)]
module 0x42::pool_forall_exists_fail;

#[spec_only]
use prover::prover::{forall, exists, ensures};

#[ext(pure)]
fun gt_50(x: &u64): bool {
    *x > 50
}

#[spec(prove)]
fun test_forall_and_exists_no_pool() {
    let not_all = !forall!<u64>(|x| gt_50(x));
    let some_exist = exists!<u64>(|x| gt_50(x));
    ensures(not_all && some_exist);
}
