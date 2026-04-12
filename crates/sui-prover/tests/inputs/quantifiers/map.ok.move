#[allow(unused)]
module 0x42::quantifiers_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::map;

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
    ensures(map!<u64, u64>(&v, |x| x_plus_10(x)) == vector[20, 30, 20, 40]);
}

// Empty-vector edge case.
#[spec(prove)]
fun test_empty() {
    let empty: vector<u64> = vector[];
    ensures(map!<u64, u64>(&empty, |x| x_plus_10(x)) == vector[]);
}
