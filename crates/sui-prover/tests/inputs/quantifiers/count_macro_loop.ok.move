// ensure that code using vector::count can be proved.

module 0x42::count_macro_loop_ok;

use prover::prover::ensures;
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun is_small(x: &u64): bool {
    *x <= 256
}

#[spec_only(loop_inv(target=count_small)), ext(no_abort)]
fun count_small_invariant(v__3: &vector<u64>, i: u64, count: u64): bool {
    i <= v__3.length() && count <= i && count == count_range!(v__3, 0, i, |j| is_small(j))
}

fun count_small(v: &vector<u64>): u64 {
    v.count!(|j| is_small(j))
}

#[spec(prove)]
fun count_small_spec(v: &vector<u64>): u64 {
    let r = count_small(v);
    ensures(r == count!(v, |j| is_small(j)));
    r
}
