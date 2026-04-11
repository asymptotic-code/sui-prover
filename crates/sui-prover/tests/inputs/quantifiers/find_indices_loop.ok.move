// ensure that a code loop implementing `find_indices` can be proved.

module 0x42::find_indices_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{find_indices, find_indices_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x) % 2 == 1
}

fun find_odd_indices(v: &vector<u64>): vector<u64> {
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(i <= v.length() && r == find_indices_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            r.push_back(i);
        };
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun find_odd_indices_spec(v: &vector<u64>): vector<u64> {
    let r = find_odd_indices(v);
    ensures(r == find_indices!(v, |j| is_odd(j)));
    r
}
