// Tests the split axiom for sum_map:
//   sum_map_range(v, 0, k) + sum_map_range(v, k, n) == sum_map(v, 0, n)
// The vector and split point are symbolic, so the proof cannot proceed
// by unfolding — it must use the split axiom.

#[allow(unused)]
module 0x42::quantifiers_sum_map_split_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::{sum_map, sum_map_range};

#[ext(pure)]
fun double(x: &u64): u64 {
    if (*x > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        2 * (*x)
    }
}

#[spec(prove)]
fun test_sum_map_split(v: &vector<u64>, k: u64) {
    let n = vector::length(v);
    requires(k <= n);
    ensures(
        sum_map_range!<u64, u64>(v, 0, k, |x| double(x))
            .add(sum_map_range!<u64, u64>(v, k, n, |x| double(x)))
            == sum_map!<u64, u64>(v, |x| double(x))
    );
}

#[spec(prove)]
fun test_sum_map_split_three_way(v: &vector<u64>, a: u64, b: u64) {
    let n = vector::length(v);
    requires(a <= b && b <= n);
    ensures(
        sum_map_range!<u64, u64>(v, 0, a, |x| double(x))
            .add(sum_map_range!<u64, u64>(v, a, b, |x| double(x)))
            .add(sum_map_range!<u64, u64>(v, b, n, |x| double(x)))
            == sum_map!<u64, u64>(v, |x| double(x))
    );
}
