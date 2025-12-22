module 0x42::simple_axiom;

use prover::prover::ensures;
use prover::vector_iter::{sum_range, filter_range};

#[ext(pure)]
fun is_qualified(x: &u8): bool {
    *x > 1 && *x < 20 && *x % 2 == 0
}

#[ext(pure)]
fun sums<T>(y: &vector<T>): bool {
    sum_range(y, 0, 3).gt(5u8.to_int()) && sum_range(y, 0, 3).lt(25u8.to_int())
}

#[spec_only(axiom)]
fun f_axiom(v: &vector<u8>): bool {
    let y = filter_range!<u8>(v, 0, 3, |x| is_qualified(x));
    sums<u8>(y)
}

public fun foo(_v: &vector<u8>) {
  assert!(true);
}

#[spec(prove)]
public fun foo_spec(_v: &vector<u8>) {
    foo(_v);
    ensures(true);
}
