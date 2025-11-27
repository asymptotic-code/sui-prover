#[allow(unused)]
module 0x42::quantifiers_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{map, filter, find, find_index, find_indices, count, any, all, sum, sum_map};

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
    // ensures(filter!<u64>(&v, |x| x_is_10(x)) == vector[10, 10]);
    // ensures(find!<u64>(&v, |x| x_is_10(x)) == option::some(10));
    // ensures(find_index!<u64>(&v, |x| x_is_10(x)) == option::some(0));
    // ensures(find_indices!<u64>(&v, |x| x_is_10(x)) == vector[0, 2]);
    // ensures(count!<u64>(&v, |x| x_is_10(x)) == 2);
    // ensures(any!<u64>(&v, |x| x_is_10(x)));
    // ensures(!all!<u64>(&v, |x| x_is_10(x)));
    // //ensures(sum<u64>(&v) == 70u64.to_int());
    // ensures(sum_map!<u64, u64>(&v, |x| x_plus_10(x)) == 110u64.to_int());
}
