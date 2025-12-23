// ensure that code using vector::find_index can be proved.

module 0x42::find_index_macro_loop_ok;

use prover::prover::ensures;
use prover::vector_iter::{find_index, any_range};

#[ext(pure)]
fun is_small(x: &u64): bool {
    *x <= 256
}

#[spec_only(loop_inv(target=find_index_small)), ext(no_abort)]
fun find_index_small_invariant(v: &vector<u64>, i: u64): bool {
    i <= v.length() && !any_range!(v, 0, i, |j| is_small(j))
}

fun find_index_small(v: &vector<u64>): Option<u64> {
    v.find_index!(|j| is_small(j))
}

#[spec(prove)]
fun find_index_small_spec(v: &vector<u64>): Option<u64> {
    let r = find_index_small(v);
    ensures(r == find_index!(v, |j| is_small(j)));
    r
}
