#[allow(unused)]
module 0x42::quantifiers_map_range_ok;

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
fun test_spec() {
    let v = vector[10, 20, 10, 30];
    ensures(map_range!<u64, u64>(&v, 0, 1, |x| x_plus_10(x)) == vector[20]);
    ensures(map_range!<u64, u64>(&v, 1, 3, |x| x_plus_10(x)) == vector[30, 20]);
}

// Empty-range edge cases: mapping over an empty range always yields an empty vector.
#[spec(prove)]
fun test_empty() {
    let empty: vector<u64> = vector[];
    ensures(map_range!<u64, u64>(&empty, 0, 0, |x| x_plus_10(x)) == vector[]);

    let v = vector[10, 20, 10, 30];
    ensures(map_range!<u64, u64>(&v, 0, 0, |x| x_plus_10(x)) == vector[]);
    ensures(map_range!<u64, u64>(&v, 2, 2, |x| x_plus_10(x)) == vector[]);
    ensures(map_range!<u64, u64>(&v, 4, 4, |x| x_plus_10(x)) == vector[]);
}
