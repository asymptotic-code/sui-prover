#[allow(unused)]
module 0x42::quantifiers_funs_aborts_fail;

#[mode(spec), ext(spec_only)]
use prover::prover::{exists, ensures};


#[ext(pure)]
fun x_is_10_aborts(x: &u64): bool {
    assert!(x == 10); // function can abort
    x == 10
}

#[mode(spec), ext(spec(prove))]
fun test_spec() {
    ensures(exists!<u64>(|x| x_is_10_aborts(x)));
}
