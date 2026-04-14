module 0x42::pure_eq;

use prover::prover::{requires, ensures};

#[ext(pure)]
fun eq(a: &Option<u8>, b: &Option<u8>): bool {
    a == b
}

#[spec(prove)]
fun eq_spec(a: &Option<u8>, b: &Option<u8>): bool {
    requires(a == b);
    let r = eq(a, b);
    ensures(r);
    r
}

#[ext(pure)]
fun vec_eq(a: &vector<u8>, b: &vector<u8>): bool {
    a == b
}

#[spec(prove)]
fun vec_eq_spec(a: &vector<u8>, b: &vector<u8>): bool {
    requires(a == b);
    let r = vec_eq(a, b);
    ensures(r);
    r
}
