#[allow(unused)]
module 0x42::quantifiers_sum_map_ok;

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

#[ext(pure)]
fun x_minus_5(x: &u64): u64 {
    if (*x < 5) {
        0
    } else {
        *x - 5
    }
}

#[spec(prove)]
fun test_sum_map() {
    let v = vector[10, 20, 10, 20];

    ensures(sum_map!<u64, u64>(&v, |x| x_minus_5(x)) == 40u64.to_int());
    ensures(sum_map!<u64, u64>(&v, |x| x_plus_10(x)) == 100u64.to_int());

    ensures(sum_map_range!<u64, u64>(&v, 2, 3, |x| x_minus_5(x)) == 5u64.to_int());
    ensures(sum_map_range!<u64, u64>(&v, 1, 4, |x| x_minus_5(x)) == 35u64.to_int());
    ensures(sum_map_range!<u64, u64>(&v, 0, 1, |x| x_plus_10(x)) == 20u64.to_int());
    ensures(sum_map_range!<u64, u64>(&v, 1, 3, |x| x_plus_10(x)) == 50u64.to_int());
}
