#[allow(unused)]
module 0x42::macro_quant;

#[spec_only]
use prover::prover::{forall, exists, ensures};

#[spec_only]
use prover::vec::{map, filter, find, find_index, find_indices, count, any, all, sum, sum_map};

#[spec_only]
fun x_is_10(x: &u64): bool {
    x == 10
}

#[spec_only]
fun x_is_gte_0(x: &u64): bool {
    *x >= 0
}

#[ext(no_abort)]
fun x_plus_10(x: &u64): u64 {
    if (*x < std::u64::max_value!() - 10) {
        *x + 10
    } else {
        std::u64::max_value!()
    }
}

#[spec(prove)]
fun test_spec() {
    let positive = forall!<u64>(|x| x_is_gte_0(x));
    ensures(positive);
    ensures(exists!<u64>(|x| x_is_10(x)));
    let v = vector[10, 20, 10, 30];
    let a = 5;
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
