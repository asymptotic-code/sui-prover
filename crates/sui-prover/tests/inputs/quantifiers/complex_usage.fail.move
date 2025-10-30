#[allow(unused)]
module 0x42::quantifiers_complex_usage;

#[spec_only]
use prover::prover::{exists, ensures, invariant};
use prover::vector_iter::map;

fun vec_leq(u: vector<u8>, v: vector<u8>): bool {
    if (u.length() > v.length()) {
        return false;
    };
    let mut i = 0;
    invariant!(|| ensures(i <= u.length() && !exists!<u64>(|j| *j <= i && u[*j] > v[*j])));
    while (i < u.length()) {
        if (u[i] > v[i]) {
            return false;
        };
        i = i+1;
    };
    true
}

#[spec(prove)]
fun vec_leq_spec(u: vector<u8>, v: vector<u8>): bool {
    vec_leq(u, v)
}
