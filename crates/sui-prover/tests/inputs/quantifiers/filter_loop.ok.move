// ensure that a code loop implementing `filter` can be proved.

module 0x42::filter_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{filter, filter_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x) % 2 == 1
}

fun filter_odd(v: &vector<u64>): vector<u64> {
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(i <= v.length() && r == filter_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            r.push_back(v[i]);
        };
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun filter_odd_spec(v: &vector<u64>): vector<u64> {
    let r = filter_odd(v);
    ensures(r == filter!(v, |j| is_odd(j)));
    r
}
