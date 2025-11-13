module 0x42::loop_invariant_external_invalid_arg_name_macro_fail;

use prover::prover::ensures;

macro fun empty_macro() {
    let mut _s: u128 = 0;
}

macro fun test_loop($n: u64): u128 {
    let mut s: u128 = 0;
    let mut i = 0;

    while (i < $n) {
        i = i + 1;
        s = s + (i as u128);
    };
    s
}

macro fun test_loop_2($n: u64): u128 {
    let mut s: u128 = 0;
    let mut i = 0;

    while (i < $n) {
        i = i + 1;
        s = s + (i as u128);
    };
    s
}

#[spec_only(loop_inv(target = test_spec))]
#[ext(no_abort)]
fun loop_inv(i: u64, n: u64, compare: u128): bool {
    i <= n && (compare == (i as u128) * ((i as u128) + 1) / 2)
}

#[spec(prove)]
fun test_spec(n: u64): u128 {
    let s = test_loop!(n);
    empty_macro!();
    let s2 = test_loop_2!(n);
    let s3 = test_loop!(n);
    ensures(s == (n as u128) * ((n as u128) + 1) / 2);
    let res = s + s2 + s3;
    res
}
