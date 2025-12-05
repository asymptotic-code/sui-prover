#[allow(unused)]
module 0x42::issue_329;

#[spec_only]
use prover::prover::requires;
#[spec_only]
use prover::vector_iter::{all, any};

#[ext(pure)]
fun x_is_10(x: &u64): bool {
    x == 10
}

#[ext(no_abort)]
fun some_x_is_10(v: &vector<u64>): bool {
    // NOTE: workaround for issue #329: using an extra.bpl + no_abort instead pure will allow to do it bacause nested quantifiers are not supported yet
    any!(v, |x| x_is_10(x))
}

#[spec(prove)]
fun test_spec(v: &vector<vector<u64>>) {
    requires(all!(v, |u| some_x_is_10(u)));
}
