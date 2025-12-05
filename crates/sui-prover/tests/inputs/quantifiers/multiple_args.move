#[allow(unused)]
module 0x42::quantifiers_multiple_args;

#[spec_only]
use prover::prover::{forall, exists, ensures};
use prover::vector_iter::map;

public struct S has copy, drop { f: u64, g: u64 }

fun get_f(s: S): u64 {
    s.f
}

fun get_g(s: S): u64 {
    s.g
}

#[ext(pure)]
fun is_greater_or_equal(a: u64, x: u64, b: u64): bool {
    x >= a && x >= b
}

#[ext(pure)]
fun sum3(a: u64, b: u64, c: u64): u128 {
    (a as u128) + (b  as u128) + (c as u128)
}

#[ext(pure)]
fun all_is_positive(a: u64, x: u64, b: u64): bool {
    a >= 0 && b >= 0 && x >= 0
}

#[spec(prove)]
fun extra_exists_spec(a: u64, b: u64) {
    ensures(exists!<u64>(|x| is_greater_or_equal(a, *x, b)));
}

#[spec(prove, no_opaque)]
fun extra_forall_spec(s: S) {
    let a = get_f(s);
    let b = get_g(s);
    ensures(forall!<u64>(|x| all_is_positive(*x, a, b)));
}

#[spec(prove, no_opaque)]
fun extra_props_forall_spec(s: S) {
    ensures(forall!<u64>(|x| all_is_positive(s.f, s.g, *x)));
}

#[spec(prove)]
fun extra_sum_spec() {
    let v = vector[10, 20, 10, 30];
    let b = 10;
    let a = 5;
    ensures(map!<u64, u128>(&v, |x| sum3(a, b, *x)) == vector[25, 35, 25, 45]);
}
