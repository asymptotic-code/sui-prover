// ensure that a code loop implementing `any` can be proved.

module 0x42::any_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{any, any_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x)%2 == 1
}

fun any_odd(v: &vector<u64>): bool {
    let mut i = 0;
    invariant!(|| ensures(!any_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            return true
        };
        i = i + 1;
    };
    false
}

#[spec(prove)]
fun any_odd_spec(v: &vector<u64>): bool {
    let r = any_odd(v);
    ensures(r == any!(v, |j| is_odd(j)));
    r
}
