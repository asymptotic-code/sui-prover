#[allow(unused)]
module 0x42::quantifiers_find_find_index_ok;

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
    let v = vector[10, 20, 10, 30];

    let result1 = find!<u64>(&v, |x| x_is_10(x));
    ensures(option::is_some(result1));
    ensures(*option::borrow(result1) == 10);

    let result2 = find!<u64>(&v, |x| x_is_20(x));
    ensures(option::is_some(result2));
    ensures(*option::borrow(result2) == 20);

    let result3 = find!<u64>(&v, |x| x_is_greater_than_100(x));
    ensures(option::is_none(result3));

    let v2: vector<u64> = vector[];

    let result4 = find!<u64>(&v2, |x| x_is_10(x));
    ensures(option::is_none(result4));
}

#[spec(prove)]
fun test_find_index() {
    let v = vector[10, 20, 10, 30];

    let idx1 = find_index!<u64>(&v, |x| x_is_10(x));
    ensures(option::is_some(&idx1));
    ensures(*option::borrow(&idx1) == 0);

    let idx2 = find_index!<u64>(&v, |x| x_is_20(x));
    ensures(option::is_some(&idx2));
    ensures(*option::borrow(&idx2) == 1);

    let idx3 = find_index!<u64>(&v, |x| x_is_greater_than_100(x));
    ensures(option::is_none(&idx3));

    let v2: vector<u64> = vector[];
    let idx4 = find_index!<u64>(&v2, |x| x_is_10(x));
    ensures(option::is_none(&idx4));
}
