// Stress test: sum_map on a larger concrete vector.

#[allow(unused)]
module 0x42::quantifiers_sum_map_big_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::sum_map;

#[ext(pure)]
fun double(x: &u64): u64 {
    if (*x > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        *x * 2
    }
}

#[spec(prove)]
fun test_sum_map_big() {
    let v = vector[1, 2, 3, 4, 5, 6, 7, 8];
    // Sum of doubles: 2 * (1+2+...+8) = 2 * 36 = 72
    ensures(sum_map!<u64, u64>(&v, |x| double(x)) == 72u64.to_int());
}
