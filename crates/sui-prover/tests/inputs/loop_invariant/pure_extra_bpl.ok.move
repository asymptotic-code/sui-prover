#[allow(unused)]
module 0x42::pure_extra_bpl_loop_inv;

use prover::prover::ensures;

// Native pure function whose body is provided via extra_bpl
#[ext(pure), spec_only(extra_bpl = b"pure_extra_bpl.ok.bpl")]
native fun sum_up_to(n: u128): u128;

fun compute_sum(n: u64): u128 {
    let mut s: u128 = 0;
    let mut i: u64 = 0;
    while (i < n) {
        i = i + 1;
        s = s + (i as u128);
    };
    s
}

#[ext(no_abort), spec_only(loop_inv(target = compute_sum))]
fun compute_sum_inv(i: u64, n: u64, s: u128): bool {
    i <= n && s == sum_up_to((i as u128))
}

#[spec(prove, extra_bpl = b"pure_extra_bpl.ok.bpl")]
fun compute_sum_spec(n: u64): u128 {
    let r = compute_sum(n);
    ensures(r == sum_up_to((n as u128)));
    r
}
