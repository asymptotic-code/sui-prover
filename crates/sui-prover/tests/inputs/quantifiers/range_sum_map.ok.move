#[allow(unused)]
module 0x42::quantifiers_range_sum_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_sum_map;

#[ext(pure)]
fun identity(x: u64): u64 {
    x
}

#[ext(pure)]
fun double(x: u64): u64 {
    if (x > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        2 * x
    }
}

#[spec(prove, extra_bpl = b"range_sum_map.ok.bpl")]
fun test_range_sum_map() {
    // Sum of i for i in [0, 4) = 0 + 1 + 2 + 3 = 6
    ensures(range_sum_map!<u64>(0, 4, |x| identity(x)) == 6u64.to_int());

    // Sum of i for i in [1, 5) = 1 + 2 + 3 + 4 = 10
    ensures(range_sum_map!<u64>(1, 5, |x| identity(x)) == 10u64.to_int());

    // Sum of 2*i for i in [0, 4) = 0 + 2 + 4 + 6 = 12
    ensures(range_sum_map!<u64>(0, 4, |x| double(x)) == 12u64.to_int());

    // Empty range should return 0
    ensures(range_sum_map!<u64>(0, 0, |x| identity(x)) == 0u64.to_int());

    // Range where end <= start should return 0
    ensures(range_sum_map!<u64>(5, 3, |x| identity(x)) == 0u64.to_int());
}
