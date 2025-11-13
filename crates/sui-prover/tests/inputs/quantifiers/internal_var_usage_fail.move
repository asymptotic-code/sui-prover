#[allow(unused)]
module 0x42::quantifiers_complex_usage;

#[spec_only]
use prover::prover::{exists, ensures, requires, invariant};
use prover::vector_iter::map;

#[ext(no_abort)]
fun invariant_expression(j: u64, i: u64, u_j: u8, v_i: u8): bool {
    j <= i && u_j > v_i
}

fun vec_leq(i: u64): bool { // for any i exists j <= i such that u[j] > v[j]
   let v: vector<u8> = vector[10, 20, 30, 40];
   let u: vector<u8> = vector[15, 25, 35, 45];
   exists!<u64>(|j| invariant_expression(*j, i, u[*j], v[i]))
}

#[spec(prove)]
fun vec_leq_spec(i: u64): bool {
    requires(i < 4);
    let res = vec_leq(i);
    ensures(res);
    res
}
