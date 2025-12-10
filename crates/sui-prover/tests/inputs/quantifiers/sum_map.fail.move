#[allow(unused)]
module 0x42::quantifiers_sum_map_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{sum_map, sum_map_range};

#[ext(pure)]
fun x_plus_10(x: &u64): u64 {
    if (*x > std::u64::max_value!() - 10) {
        std::u64::max_value!()
    } else {
        *x + 10
    }
}

#[spec(prove)]
fun test_sum_map_fail() {
    let v = vector[10, 20, 30, 40];

    // This should fail because sum_map is 140
    ensures(sum_map!<u64, u64>(&v, |x| x_plus_10(x)) == 100u64.to_int());
}

#[spec(prove)]
fun test_sum_map_range_fail() {
    let v = vector[100, 200, 300, 400];

    // This should fail because range [0, 2) sum is 320
    ensures(sum_map_range!<u64, u64>(&v, 0, 2, |x| x_plus_10(x)) == 300u64.to_int());
}
