#[allow(unused)]
module 0x42::quantifiers_find_find_index_fail;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{find, find_index};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_20(x: &u64): bool {
    *x == 20
}

#[ext(pure)]
fun x_is_greater_than_100(x: &u64): bool {
    *x > 100
}

#[spec(prove)]
fun test_find() {
    let v: vector<u64> = vector[];
    let result4 = find!<u64>(&v, |x| x_is_10(x));
    ensures(option::is_some(result4)); // should fail because here we expect none
}

#[spec(prove)]
fun test_find_index() {
    let v = vector[10, 20, 10, 30];

    let idx1 = find_index!<u64>(&v, |x| x_is_10(x));
    ensures(option::is_some(&idx1));
    ensures(*option::borrow(&idx1) == 1); // should fail because here we expect index 0
}
