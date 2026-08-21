module 0x42::loop_invariant_external_mut_ref_ok;

use prover::prover::ensures;

#[mode(spec), ext(spec(loop_inv(target = test_spec)), no_abort)]
#[allow(unused_function)]
fun loop_inv(i: u64, n: u64, p: &u128): bool {
    i <= n && (*p == (i as u128) * ((i as u128) + 1) / 2)
}

#[spec(prove)]
fun test_spec(n: u64): u128 {
    let mut s: u128 = 0;
    let mut i = 0;
    let p: &mut u128 = &mut s;

    while (i < n) {
        i = i + 1;
        *p = *p + (i as u128);
    };

    ensures(s == (n as u128) * ((n as u128) + 1) / 2);
    s
}
