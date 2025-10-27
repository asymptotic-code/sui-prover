module 0x42::loop_invariant_external_tests;

use prover::prover::{ensures};

#[spec(prove)]
fun test0_spec(n: u64) {
    let mut i = 0;

    while (i < n) {
        i = i + 1;
    };

    ensures(i == n);
}

#[spec_only(loop_inv(target = test0_spec))]
fun loop_inv_0(i: u64, n: u64): bool {
    i <= n
}

// #[spec(prove)]
// fun test1_spec(n: u64): u128 {
//     let mut s: u128 = 0;
//     let mut i = 0;

//     invariant!(|| {
//         ensures(i <= n && s == (i as u128) * ((i as u128) + 1) / 2);
//     });
//     while (i < n) {
//         i = i + 1;
//         s = s + (i as u128);
//     };

//     ensures(s == (n as u128) * ((n as u128) + 1) / 2);
//     s
// }

// #[spec(prove)]
// fun test2_spec(n: u64): u128 {
//     let mut s: u128 = 0;
//     let mut i = 0;

//     invariant!(|| {
//         ensures(i <= n);
//         ensures(s == (i as u128) * ((i as u128) + 1) / 2);
//     });
//     while (i < n) {
//         i = i + 1;
//         s = s + (i as u128);
//     };

//     ensures(s == (n as u128) * ((n as u128) + 1) / 2);
//     s
// }

// #[spec(prove)]
// fun test3_spec(mut n: u64): u128 {
//     let mut s: u128 = 0;

//     let old_n = old!(&n);
//     invariant!(|| {
//         ensures(n <= *old_n);
//         ensures(s == ((*old_n as u128) - (n as u128)) * ((*old_n as u128) + (n as u128) + 1) / 2);
//     });
//     while (n > 0) {
//         s = s + (n as u128);
//         n = n - 1;
//     };

//     ensures(s == (*old_n as u128) * ((*old_n as u128) + 1) / 2);
//     s
// }

// #[spec(prove)]
// fun test4_spec(n: u64): u128 {
//     requires(0 < n);

//     let mut s: u128 = 0;
//     let mut i = 0;

//     invariant!(|| {
//         ensures(i < n);
//         ensures(s == (i as u128) * ((i as u128) + 1) / 2);
//     });
//     loop {
//         i = i + 1;
//         s = s + (i as u128);
//         if (i >= n) {
//             break
//         }
//     };

//     ensures(s == (n as u128) * ((n as u128) + 1) / 2);
//     s
// }

// #[spec(prove, ignore_abort)]
// fun test5_spec(n: u64) {
//     let mut i = 0;

//     while (i < n) {
//         i = i + 1;
//     };

//     ensures(i >= n);
// }

// public struct SpecSum {}

// fun emit_u64(_x: u64) {}

// #[spec]
// fun emit_u64_spec(x: u64) {
//     ghost::declare_global_mut<SpecSum, Integer>();
//     let old_sum = *ghost::global<SpecSum, Integer>();
//     emit_u64(x);
//     ensures(ghost::global<SpecSum, Integer>() == old_sum.add(x.to_int()));
// }

// #[spec(prove)]
// fun test6_spec(n: u64) {
//     ghost::declare_global_mut<SpecSum, Integer>();
//     requires(ghost::global<SpecSum, Integer>() == 0u64.to_int());

//     let mut i = 0;

//     invariant!(|| {
//         ensures(i <= n);
//         ensures(
//             ghost::global<SpecSum, Integer>() == ((i as u128) * ((i as u128) + 1) / 2).to_int(),
//         );
//     });
//     while (i < n) {
//         i = i + 1;
//         emit_u64(i);
//     };

//     ensures(i == n);
//     ensures(ghost::global<SpecSum, Integer>() == ((n as u128) * ((n as u128) + 1) / 2).to_int());
// }

// #[spec(prove, ignore_abort)]
// fun test7_spec(s: &mut u128, n: u64) {
//     let old_s = old!(s);

//     let mut i = 0;

//     invariant!(|| {
//         ensures(i <= n);
//         ensures(s == *old_s + (i as u128) * ((i as u128) + 1) / 2);
//     });
//     while (i < n) {
//         i = i + 1;
//         *s = *s + (i as u128);
//     };

//     ensures(s == *old_s + (n as u128) * ((n as u128) + 1) / 2);
//     ensures(i == n);
// }