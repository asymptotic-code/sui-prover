// ensure that a code loop implementing `find` can be proved.

module 0x42::find_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{find, any_range};

#[ext(pure)]
fun is_odd(x: &u8): bool {
    (*x)%2 == 1
}

fun find_odd(v: &vector<u8>): Option<u8> {
    let mut i = 0;
    invariant!(|| ensures(i <= v.length() && !any_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            return option::some(v[i])
        };
        i = i + 1;
    };
    option::none()
}

#[spec(prove)]
fun find_odd_spec(v: &vector<u8>): Option<u8> {
    let r = find_odd(v);
    ensures(r == find!(v, |j| is_odd(j)));
    r
}
