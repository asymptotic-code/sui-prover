// ensure that code using vector::all can be proved.

module 0x42::all_macro_loop_ok;

use prover::prover::ensures;
use prover::vector_iter::{all, all_range};

#[ext(pure)]
fun is_small(x: &u64): bool {
    *x <= 256
}

#[spec_only(loop_inv(target=all_small)), ext(no_abort)]
fun all_small_invariant(v: &vector<u64>, i: u64): bool {
    all_range!(v, 0, i, |j| is_small(j))
}

fun all_small(v: &vector<u64>): bool {
    v.all!(|j| is_small(j))
}

#[spec(prove)]
fun all_small_spec(v: &vector<u64>): bool {
    let r = all_small(v);
    ensures(r == all!(v, |j| is_small(j)));
    r
}
