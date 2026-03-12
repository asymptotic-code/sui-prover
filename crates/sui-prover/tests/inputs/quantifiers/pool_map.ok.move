#[allow(unused)]
module 0x42::pool_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::map;

#[ext(pure)]
fun add_one(x: &u64): u64 {
    if (*x < std::u64::max_value!()) {
        *x + 1
    } else {
        std::u64::max_value!()
    }
}

#[spec(prove)]
fun test_pool_map_spec() {
    let v = vector[1, 2, 3];
    let result = map!<u64, u64>(&v, |x| add_one(x));
    ensures(result == vector[2, 3, 4]);
}
