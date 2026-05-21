/// Regression: a void loop_invariant function whose parameter name does not
/// match any local in the target used to panic in inline_void_invariant with
/// "index out of bounds" instead of reporting a diagnostic.
module 0x42::loop_invariant_external_void_invalid_arg_name_fail;

use prover::prover::ensures;

#[spec_only(loop_inv(target = test_spec))]
#[ext(no_abort)]
fun loop_inv(i: u64, n: u64, compare: u128) {
    ensures(i <= n);
    ensures(compare == (i as u128) * ((i as u128) + 1) / 2);
}

#[spec(prove)]
fun test_spec(n: u64): u128 {
    let mut s: u128 = 0;
    let mut i = 0;

    while (i < n) {
        i = i + 1;
        s = s + (i as u128);
    };

    ensures(s == (n as u128) * ((n as u128) + 1) / 2);
    s
}
