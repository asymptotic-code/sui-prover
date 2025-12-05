#[allow(unused)]
module 0x42::quantifiers_map_ok;

#[spec_only]
use prover::prover::{ensures,requires};

#[spec_only]
use prover::vector_iter::{map_range, map};

public struct S {}

#[ext(pure)]
fun to_zero(x: &S): u8 {
    0
}

#[spec(prove)]
fun map_test(v: &vector<S>) {
    let r = map!(v, |e| to_zero(e));
    ensures(r == r);
}

#[spec(prove)]
fun map_range_test(v: &vector<S>) {
    requires(vector::length(v) >= 3);
    let r = map_range!(v, 0, 3, |e| to_zero(e));
    ensures(r == r);
}
