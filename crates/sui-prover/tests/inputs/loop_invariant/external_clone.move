module 0x42::loop_invariant_external_clone;

use prover::prover::{ensures, clone};

#[spec_only(loop_inv(target = test_spec))]
#[ext(pure)]
fun loop_inv(n: u64, __old_n: u64, s: u128): bool {
    n <= __old_n && (s == ((__old_n as u128) - (n as u128)) * ((__old_n as u128) + (n as u128) + 1) / 2)
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
