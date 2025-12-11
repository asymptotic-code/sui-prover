// ensure that a code loop implementing `all` can be proved.

module 0x42::all_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{all, all_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x)%2 == 1
}

fun all_odd(v: &vector<u64>): bool {
    let mut i = 0;
    invariant!(|| ensures(all_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (! is_odd(&v[i])) {
            return false
        };
        i = i + 1;
    };
    true
}

#[spec(prove)]
fun all_odd_spec(v: &vector<u64>): bool {
    let r = all_odd(v);
    ensures(r == all!(v, |j| is_odd(j)));
    r
}
