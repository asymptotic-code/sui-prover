// ensure that code using vector::any can be proved.

module 0x42::any_macro_loop_ok;

use prover::prover::ensures;
use prover::vector_iter::{any, any_range};

#[ext(pure)]
fun is_small(x: &u64): bool {
    *x <= 256
}

#[mode(spec), ext(spec(loop_inv(target=any_small)), no_abort)]
#[allow(unused_function)]
fun any_small_invariant(v: &vector<u64>, i: u64): bool {
    ! any_range!(v, 0, i, |j| is_small(j))
}

fun any_small(v: &vector<u64>): bool {
    v.any!(|j| is_small(j))
}

#[spec(prove)]
fun any_small_spec(v: &vector<u64>): bool {
    let r = any_small(v);
    ensures(r == any!(v, |j| is_small(j)));
    r
}
