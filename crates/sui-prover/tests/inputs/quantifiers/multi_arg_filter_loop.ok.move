// Loop test exercising filter with a predicate that captures a runtime
// parameter (`threshold`). Stresses the extra-captured-args path (CAT) in
// filter's recursive axioms.

module 0x42::multi_arg_filter_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{filter, filter_range};

#[ext(pure)]
fun greater_than(x: &u64, threshold: u64): bool {
    *x > threshold
}

fun filter_greater_than(v: &vector<u64>, threshold: u64): vector<u64> {
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(
        i <= v.length()
            && r == filter_range!(v, 0, i, |j| greater_than(j, threshold))
    ));
    while (i < v.length()) {
        if (greater_than(&v[i], threshold)) {
            r.push_back(v[i]);
        };
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun filter_greater_than_spec(v: &vector<u64>, threshold: u64): vector<u64> {
    let r = filter_greater_than(v, threshold);
    ensures(r == filter!(v, |j| greater_than(j, threshold)));
    r
}
