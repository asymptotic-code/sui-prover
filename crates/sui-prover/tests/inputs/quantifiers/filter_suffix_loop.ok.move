// Loop test with a suffix invariant for `filter`, expressed via concat. The
// invariant
//
//   concat(r, filter_range(v, i, n, p)) == filter(v, p)
//
// needs the start-step direction of filter's recursive axiom to verify.

module 0x42::filter_suffix_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{filter, filter_range, concat};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x) % 2 == 1
}

fun filter_odds(v: &vector<u64>): vector<u64> {
    let n = vector::length(v);
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(
        i <= n
            && concat(&r, filter_range!(v, i, n, |x| is_odd(x))) == *filter!(v, |x| is_odd(x))
    ));
    while (i < n) {
        if (is_odd(vector::borrow(v, i))) {
            r.push_back(*vector::borrow(v, i));
        };
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun filter_odds_spec(v: &vector<u64>): vector<u64> {
    let r = filter_odds(v);
    ensures(r == *filter!(v, |x| is_odd(x)));
    r
}
