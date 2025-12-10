module 0x42::loop_invariant_external_return_type_fail;

use prover::prover::ensures;

#[spec_only(loop_inv(target = test_spec))]
#[ext(no_abort)]
fun loop_inv(i: u64, n: u64, s: u128): u64 {
    //(i <= n, (s == (i as u128) * ((i as u128) + 1) / 2))
    n
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
