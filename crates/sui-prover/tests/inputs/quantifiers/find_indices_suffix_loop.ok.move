// Loop test with a suffix invariant for `find_indices`, expressed via concat.
// The invariant
//
//   append_pure(r, find_indices_range(v, i, n, p)) == find_indices(v, p)
//
// needs the start-step direction of find_indices's recursive axiom to verify
// the loop body. find_indices uses compound-trigger recursive axioms so this
// works without polluting concrete-vector verifications.

module 0x42::find_indices_suffix_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{find_indices, find_indices_range};
use std::vector::append_pure;

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x) % 2 == 1
}

fun find_odd_indices(v: &vector<u64>): vector<u64> {
    let n = vector::length(v);
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(
        i <= n
            && append_pure(&r, find_indices_range!(v, i, n, |x| is_odd(x)))
                == *find_indices!(v, |x| is_odd(x))
    ));
    while (i < n) {
        if (is_odd(vector::borrow(v, i))) {
            r.push_back(i);
        };
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun find_odd_indices_spec(v: &vector<u64>): vector<u64> {
    let r = find_odd_indices(v);
    ensures(r == *find_indices!(v, |x| is_odd(x)));
    r
}
