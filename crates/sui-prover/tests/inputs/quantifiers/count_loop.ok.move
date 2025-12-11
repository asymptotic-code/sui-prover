// ensure that a code loop implementing `count` can be proved.

module 0x42::count_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x)%2 == 1
}

fun count_odd(v: &vector<u64>): u64 {
    let mut i = 0;
    let mut c = 0;
    invariant!(|| ensures(i <= v.length() && c <= i && c == count_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            c = c + 1
        };
        i = i + 1;
    };
    c
}

#[spec(prove)]
fun count_odd_spec(v: &vector<u64>): u64 {
    let r = count_odd(v);
    ensures(r == count!(v, |j| is_odd(j)));
    r
}
