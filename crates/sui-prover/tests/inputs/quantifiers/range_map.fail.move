#[allow(unused)]
module 0x42::quantifiers_range_map_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_map;

#[ext(pure)]
fun x_plus_10(x: u64): u64 {
    if (x < std::u64::max_value!() - 10) {
        x + 10
    } else {
        std::u64::max_value!()
    }
}

#[spec(prove)]
fun test_map_range_wrong_result() {    
    ensures(range_map!<u64>(3, 5, |x| x_plus_10(x)) == vector[13]); // FAIL: should be 2 elements
}

#[spec(prove)]
fun test_map_range_wrong_subrange() {
    ensures(range_map!<u64>(1, 3, |x| x_plus_10(x)) == vector[21, 40]); // FAIL: should be [11, 12]
}
