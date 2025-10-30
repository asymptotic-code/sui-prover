module 0x42::loop_invariant_external_tests;

use prover::prover::{requires, ensures, old};
use prover::ghost;
use std::integer::Integer;

#[spec_only(loop_inv(target = test0_spec))]
fun loop_inv_0(i: u64, n: u64): bool {
    i <= n
}

#[spec_only(loop_inv(target = test1_spec))]
fun loop_inv_1(i: u64, n: u64, s: u128): bool {
    i <= n && (s == (i as u128) * ((i as u128) + 1) / 2)
}

#[spec_only(loop_inv(target = test2_spec))]
fun loop_inv_2(i: u64, n: u64, s: u128): bool {
    i <= n && (s == (i as u128) * ((i as u128) + 1) / 2)
}

#[spec_only(loop_inv(target = test3_spec))]
fun loop_inv_3(n: u64, old_n: u64, s: u128): bool {
    n <= old_n && (s == ((old_n as u128) - (n as u128)) * ((old_n as u128) + (n as u128) + 1) / 2)
}

#[spec_only(loop_inv(target = test4_spec))]
fun loop_inv_4(i: u64, n: u64, s: u128): bool {
    i <= n && (s == (i as u128) * ((i as u128) + 1) / 2)
}

#[spec_only(loop_inv(target = test5_spec))]
fun loop_inv_5(i: u64, n: u64): bool {
    i <= n && (ghost::global<SpecSum, Integer>() == ((i as u128) * ((i as u128) + 1) / 2).to_int())
}

#[spec_only(loop_inv(target = test6_spec))]
fun loop_inv_6(i: u64, n: u64, old_s: u128, s: u128): bool {
    i <= n && (s == old_s + (i as u128) * ((i as u128) + 1) / 2)
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
fun test2_spec(n: u64): u128 {
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
fun test3_spec(mut n: u64): u128 {
    let mut s: u128 = 0;

    let old_n: &u64 = old!(&n);
    while (n > 0) {
        s = s + (n as u128);
        n = n - 1;
    };

    ensures(s == (*old_n as u128) * ((*old_n as u128) + 1) / 2);
    s
}

#[spec(prove)]
fun test4_spec(n: u64): u128 {
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

public struct SpecSum {}

fun emit_u64(_x: u64) {}

#[spec]
fun emit_u64_spec(x: u64) {
    ghost::declare_global_mut<SpecSum, Integer>();
    let old_sum = *ghost::global<SpecSum, Integer>();
    emit_u64(x);
    ensures(ghost::global<SpecSum, Integer>() == old_sum.add(x.to_int()));
}

#[spec(prove)]
fun test5_spec(n: u64) {
    ghost::declare_global_mut<SpecSum, Integer>();
    requires(ghost::global<SpecSum, Integer>() == 0u64.to_int());

    let mut i = 0;

    while (i < n) {
        i = i + 1;
        emit_u64(i);
    };

    ensures(i == n);
    ensures(ghost::global<SpecSum, Integer>() == ((n as u128) * ((n as u128) + 1) / 2).to_int());
}

#[spec(prove, ignore_abort)]
fun test6_spec(s: &mut u128, n: u64) {
    let old_s: &u128 = old!(s);

    let mut i = 0;

    while (i < n) {
        i = i + 1;
        *s = *s + (i as u128);
    };

    ensures(s == *old_s + (n as u128) * ((n as u128) + 1) / 2);
    ensures(i == n);
}