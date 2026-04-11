// Loop tests that exercise iterator helpers with predicates carrying captured
// context parameters. These stress the `captured_args_tail` template path for
// the recursive axioms (count, filter, find_indices, sum_map).

module 0x42::multi_arg_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{count, count_range, filter, filter_range};

#[ext(pure)]
fun greater_than(x: &u64, threshold: u64): bool {
    *x > threshold
}

// Count elements greater than a runtime threshold.
fun count_greater_than(v: &vector<u64>, threshold: u64): u64 {
    let mut i = 0;
    let mut c = 0;
    invariant!(|| ensures(
        i <= v.length()
            && c <= i
            && c == count_range!(v, 0, i, |j| greater_than(j, threshold))
    ));
    while (i < v.length()) {
        if (greater_than(&v[i], threshold)) {
            c = c + 1
        };
        i = i + 1;
    };
    c
}

#[spec(prove)]
fun count_greater_than_spec(v: &vector<u64>, threshold: u64): u64 {
    let r = count_greater_than(v, threshold);
    ensures(r == count!(v, |j| greater_than(j, threshold)));
    r
}

// Filter elements greater than a runtime threshold.
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
