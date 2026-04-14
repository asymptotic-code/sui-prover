// Tests the bounding axiom for sum_map:
//   sum_map_range(v, a, b) <= sum_map(v)
// when [a, b] is nested in [0, v.length()]. Relies on the gate that emits
// bounding only when FN's Move return type is a fixed-width unsigned int
// (here u64). Uses symbolic inputs to force the axiom to fire.

#[allow(unused)]
module 0x42::quantifiers_sum_map_bounding_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::{sum_map, sum_map_range};

#[ext(pure)]
fun plus_one(x: &u64): u64 {
    if (*x == std::u64::max_value!()) {
        std::u64::max_value!()
    } else {
        *x + 1
    }
}

#[spec(prove)]
fun test_sum_map_bounding_nested(v: &vector<u64>, a: u64, b: u64) {
    let n = vector::length(v);
    requires(a <= b && b <= n);
    ensures(
        sum_map_range!<u64, u64>(v, a, b, |x| plus_one(x))
            .lte(sum_map!<u64, u64>(v, |x| plus_one(x)))
    );
}
