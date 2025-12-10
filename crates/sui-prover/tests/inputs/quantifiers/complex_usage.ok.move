#[allow(unused)]
module 0x42::quantifiers_complex_usage;

#[spec_only]
use prover::prover::{exists, ensures, requires, invariant};
use prover::vector_iter::map;

#[ext(pure)]
fun invariant_expression(j: u64, i: u64, u: &vector<u8>, v: &vector<u8>): bool {
   j <= i && j < u.length() && i < v.length() && u[j] > v[i]
}

fun vec_leq(i: u64): bool { // for any i exists j <= i such that u[j] > v[j]
   let v: vector<u8> = vector[10, 20, 30, 40];
   let u: vector<u8> = vector[15, 25, 35, 45];
   exists!<u64>(|j| invariant_expression(*j, i, &u, &v))
}

#[spec(prove)]
fun vec_leq_spec(i: u64): bool {
    requires(i < 4);
    let res = vec_leq(i);
    ensures(res);
    res
}
