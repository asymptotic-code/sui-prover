module 0x42::loop_invariant_external_void_ok;

use prover::prover::{requires, ensures, clone};

#[spec_only(loop_inv(target = test0_spec))]
#[ext(no_abort)]
fun loop_inv_0(i: u64, n: u64) {
    ensures(i <= n);
}

#[spec_only(loop_inv(target = test1_spec))]
#[ext(no_abort)]
fun loop_inv_1(i: u64, n: u64, s: u128) {
    ensures(i <= n);
    ensures(s == (i as u128) * ((i as u128) + 1) / 2);
}

#[spec_only(loop_inv(target = test2_spec))]
#[ext(no_abort)]
fun loop_inv_2(n: u64, old_n: u64, s: u128) {
    ensures(n <= old_n);
    ensures(s == ((old_n as u128) - (n as u128)) * ((old_n as u128) + (n as u128) + 1) / 2);
}

#[spec_only(loop_inv(target = test3_spec))]
#[ext(no_abort)]
fun loop_inv_3(i: u64, n: u64, s: u128) {
    ensures(i < n);
    ensures(s == (i as u128) * ((i as u128) + 1) / 2);
}

#[spec(prove)]
fun test0_spec(n: u64) {
    let mut i = 0;

    while (i < n) {
        i = i + 1;
    };

    ensures(i == n);
}

#[spec(prove)]
fun test1_spec(n: u64): u128 {
    let mut s: u128 = 0;
    let mut i = 0;

    while (i < n) {
        i = i + 1;
        s = s + (i as u128);
    };

    ensures(s == (n as u128) * ((n as u128) + 1) / 2);
    s
}

#[spec(prove)]
fun test2_spec(mut n: u64): u128 {
    let mut s: u128 = 0;

    let old_n: &u64 = clone!(&n);
    while (n > 0) {
        s = s + (n as u128);
        n = n - 1;
    };

    ensures(s == (*old_n as u128) * ((*old_n as u128) + 1) / 2);
    s
}

#[spec(prove)]
fun test3_spec(n: u64): u128 {
    requires(0 < n);

    let mut s: u128 = 0;
    let mut i = 0;

    loop {
        i = i + 1;
        s = s + (i as u128);
        if (i >= n) {
            break
        }
    };

    ensures(s == (n as u128) * ((n as u128) + 1) / 2);
    s
}
