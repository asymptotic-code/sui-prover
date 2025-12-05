#[allow(unused)]
module 0x42::quantifiers_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::map;

public struct S {}

#[ext(no_abort)]
fun to_zero(x: &S): u8 {
    0
}

#[spec(prove)]
fun map_test(v: &vector<S>) {
    let r = map!(v, |e| to_zero(e));
    ensures(r == r);
}
