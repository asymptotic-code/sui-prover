// Loop test exercising count with a predicate that captures a runtime
// parameter (`threshold`). Stresses the `captured_args_tail` template path
// for count's recursive axioms.

module 0x42::multi_arg_count_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun greater_than(x: &u64, threshold: u64): bool {
    *x > threshold
}

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
