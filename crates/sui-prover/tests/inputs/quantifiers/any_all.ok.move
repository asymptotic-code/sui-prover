#[allow(unused)]
module 0x42::quantifiers_any_all_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::{any, all};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    *x == 10
}

#[ext(pure)]
fun x_is_positive(x: &u64): bool {
    *x > 0
}

#[ext(pure)]
fun x_is_greater_than_100(x: &u64): bool {
    *x > 100
}

#[spec(prove)]
fun test_any_all() {
    let v = vector[10, 20, 10, 30];

    // Test ANY - should return true if at least one element satisfies predicate
    ensures(any!<u64>(&v, |x| x_is_10(x)));           // true: has 10s
    ensures(any!<u64>(&v, |x| x_is_positive(x)));     // true: all are positive
    ensures(!any!<u64>(&v, |x| x_is_greater_than_100(x))); // false: none > 100
    
    // Test ALL - should return true if all elements satisfy predicate
    ensures(all!<u64>(&v, |x| x_is_positive(x)));     // true: all are positive
    ensures(!all!<u64>(&v, |x| x_is_10(x)));          // false: not all are 10
    ensures(!all!<u64>(&v, |x| x_is_greater_than_100(x))); // false: none > 100
}
