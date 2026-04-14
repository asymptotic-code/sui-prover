// Tests the split axiom for count:
//   count_range(v, 0, k) + count_range(v, k, n) == count(v, 0, n)
// The vector and split point are symbolic (not concrete), so the proof
// cannot proceed by unfolding — it must use the split axiom.

#[allow(unused)]
module 0x42::quantifiers_count_split_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun is_even(x: &u64): bool {
    (*x) % 2 == 0
}

#[spec(prove)]
fun test_count_split(v: &vector<u64>, k: u64) {
    let n = vector::length(v);
    requires(k <= n);
    ensures(
        count_range!<u64>(v, 0, k, |x| is_even(x))
            + count_range!<u64>(v, k, n, |x| is_even(x))
            == count!<u64>(v, |x| is_even(x))
    );
}

#[spec(prove)]
fun test_count_split_three_way(v: &vector<u64>, a: u64, b: u64) {
    let n = vector::length(v);
    requires(a <= b && b <= n);
    ensures(
        count_range!<u64>(v, 0, a, |x| is_even(x))
            + count_range!<u64>(v, a, b, |x| is_even(x))
            + count_range!<u64>(v, b, n, |x| is_even(x))
            == count!<u64>(v, |x| is_even(x))
    );
}
