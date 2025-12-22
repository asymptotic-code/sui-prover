module 0x42::loop_invariant_external_extra_ok;

use prover::prover::{ensures, clone};

#[spec_only(loop_inv(target = test_spec)), ext(no_abort)]
fun loop_inv(n: u64, s: u128): bool {
    let old: u64 = *clone!(&n);
    n <= old && (s == ((old as u128) - (n as u128)) * ((old as u128) + (n as u128) + 1) / 2)
}

#[spec(prove)]
fun test_spec(mut n: u64): u128 {
    let mut s: u128 = 0;

    let old_n: &u64 = clone!(&n);
    while (n > 0) {
        s = s + (n as u128);
        n = n - 1;
    };

    ensures(s == (*old_n as u128) * ((*old_n as u128) + 1) / 2);
    s
}
