// Loop test with a suffix invariant for `find_index`. The invariant says
// "no match has been found in [0, i) yet", expressed as:
//
//   find_index_range(v, 0, i, pred) == option::none()
//
// But the spec compares against the full-range result using find_index's
// start-step: find_index(v, 0, n) == find_index(v, i, n) when the prefix
// [0, i) has no match.

module 0x42::find_index_suffix_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{find_index, find_index_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x) % 2 == 1
}

// Suffix invariant: find_index_range(v, 0, i) == none means no match in [0, i),
// so find_index(v) == find_index_range(v, i, n). When we reach the end and
// still have no match, the result is none.
fun find_index_odd_suffix(v: &vector<u64>): Option<u64> {
    let n = vector::length(v);
    let mut i = 0;
    invariant!(|| ensures(
        i <= n
            && find_index_range!(v, 0, i, |j| is_odd(j)) == option::none()
    ));
    while (i < n) {
        if (is_odd(&v[i])) {
            return option::some(i)
        };
        i = i + 1;
    };
    option::none()
}

#[spec(prove)]
fun find_index_odd_suffix_spec(v: &vector<u64>): Option<u64> {
    let r = find_index_odd_suffix(v);
    ensures(r == find_index!(v, |j| is_odd(j)));
    r
}
