// Tests the singleton axiom for sum_map:
//   sum_map_range(v, i, i+1, f) == f(v[i])
// Uses a symbolic vector and index to force the axiom to fire.

#[allow(unused)]
module 0x42::quantifiers_sum_map_singleton_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_iter::sum_map_range;

#[ext(pure)]
fun plus_one(x: &u64): u64 {
    if (*x == std::u64::max_value!()) {
        std::u64::max_value!()
    } else {
        *x + 1
    }
}

#[spec(prove)]
fun test_sum_map_singleton(v: &vector<u64>, i: u64) {
    requires(i < vector::length(v));
    ensures(
        sum_map_range!<u64, u64>(v, i, i + 1, |x| plus_one(x))
            == plus_one(vector::borrow(v, i)).to_int()
    );
}
