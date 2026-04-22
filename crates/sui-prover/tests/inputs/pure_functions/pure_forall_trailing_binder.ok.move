/// Test that `forall!` inside a pure helper works when the quantified
/// parameter of the inner predicate is NOT the first parameter. Previously
/// the Boogie backend declared the bound variable with the type of
/// `get_parameter_types()[0]` instead of `[li]`, so the generated
/// `(forall x: Vec int :: ... equal_in_range(u, v, i, j, x))` mismatched
/// the predicate's trailing `int` parameter and Boogie rejected it.
module 0x42::pure_forall_trailing_binder;

#[spec_only]
use prover::prover::{ensures, forall};

#[ext(pure)]
fun equal_in_range(u: &vector<u64>, v: &vector<u64>, i: u64, j: u64, k: u64): bool {
    k < i || k >= j || k >= u.length() || k >= v.length() || u[k] == v[k]
}

#[ext(pure)]
fun equal_range(u: &vector<u64>, v: &vector<u64>, i: u64, j: u64): bool {
    forall!(|k| equal_in_range(u, v, i, j, *k))
}

#[spec(prove)]
fun verify_equal_range(): bool {
    let u = vector[1u64, 2u64, 3u64];
    let v = vector[1u64, 2u64, 3u64];
    let result = equal_range(&u, &v, 0, 3);
    ensures(result);
    result
}
