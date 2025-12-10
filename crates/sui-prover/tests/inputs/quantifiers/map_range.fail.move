#[allow(unused)]
module 0x42::quantifiers_map_range_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::map_range;

#[ext(pure)]
fun x_plus_10(x: &u64): u64 {
    if (*x < std::u64::max_value!() - 10) {
        *x + 10
    } else {
        std::u64::max_value!()
    }
}

#[spec(prove)]
fun test_map_range_wrong_result() {
    let v = vector[10, 20, 10, 30];
    
    // Should fail: mapping range [0, 1) with x_plus_10 gives [20], not [30]
    ensures(map_range!<u64, u64>(&v, 0, 1, |x| x_plus_10(x)) == vector[30]); // FAIL: should be [20]
}

#[spec(prove)]
fun test_map_range_wrong_subrange() {
    let v = vector[10, 20, 10, 30];
    
    // Should fail: mapping range [1, 3) gives [30, 20], not [20, 40]
    // Range [1, 3) contains [20, 10], so mapping gives [30, 20]
    ensures(map_range!<u64, u64>(&v, 1, 3, |x| x_plus_10(x)) == vector[20, 40]); // FAIL: should be [30, 20]
}
