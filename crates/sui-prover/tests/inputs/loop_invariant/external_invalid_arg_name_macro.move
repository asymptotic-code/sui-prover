module 0x42::loop_invariant_external_invalid_arg_name_macro_fail;

use prover::prover::ensures;

macro fun test_loop($n: u64): u128 {
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
    let res = test_loop!(n);
    ensures(res == (n as u128) * ((n as u128) + 1) / 2);
    res
}
