#[allow(unused)]
module 0x42::issue_329;

#[mode(spec)]
use prover::prover::requires;
#[mode(spec)]
use prover::vector_iter::{all, any};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    x == 10
}

#[ext(pure)]
fun some_x_is_10(v: &vector<u64>): bool {
    any!(v, |x| x_is_10(x))
}

#[spec(prove)]
fun test_spec(v: &vector<vector<u64>>) {
    requires(all!(v, |u| some_x_is_10(u)));
}
