// ensure that a code loop implementing `find_index` can be proved.

module 0x42::find_index_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{find_index, find_index_range, any_range};

#[ext(pure)]
fun is_odd(x: &u8): bool {
    (*x)%2 == 1
}

fun find_index_odd(v: &vector<u8>): Option<u64> {
    let mut i = 0;
    invariant!(|| ensures(i <= v.length() && !any_range!(v, 0, i, |j| is_odd(j))));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            return option::some(i)
        };
        i = i + 1;
    };
    option::none()
}

#[spec(prove)]
fun find_index_odd_spec(v: &vector<u8>): Option<u64> {
    let r = find_index_odd(v);
    ensures(r == find_index!(v, |j| is_odd(j)));
    r
}

// Variant using find_index_range directly in the loop invariant, which
// exercises the bidirectional incremental find_index axiom.
fun find_index_odd_direct(v: &vector<u8>): Option<u64> {
    let mut i = 0;
    invariant!(|| ensures(
        i <= v.length()
            && find_index_range!(v, 0, i, |j| is_odd(j)) == option::none()
    ));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            return option::some(i)
        };
        i = i + 1;
    };
    option::none()
}

#[spec(prove)]
fun find_index_odd_direct_spec(v: &vector<u8>): Option<u64> {
    let r = find_index_odd_direct(v);
    ensures(r == find_index!(v, |j| is_odd(j)));
    r
}
