// Tests the split axiom for range_count:
//   range_count(0, k) + range_count(k, n) == range_count(0, n)
// Symbolic bounds force the split axiom to fire rather than concrete unfolding.

#[allow(unused)]
module 0x42::quantifiers_range_count_split_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::range_count;

#[ext(pure)]
fun is_even(x: u64): bool {
    x % 2 == 0
}

#[spec(prove)]
fun test_range_count_split(n: u64, k: u64) {
    requires(k <= n);
    ensures(
        range_count!(0, k, |x| is_even(x))
            .add(range_count!(k, n, |x| is_even(x)))
            == range_count!(0, n, |x| is_even(x))
    );
}

#[spec(prove)]
fun test_range_count_split_three_way(n: u64, a: u64, b: u64) {
    requires(a <= b && b <= n);
    ensures(
        range_count!(0, a, |x| is_even(x))
            .add(range_count!(a, b, |x| is_even(x)))
            .add(range_count!(b, n, |x| is_even(x)))
            == range_count!(0, n, |x| is_even(x))
    );
}
