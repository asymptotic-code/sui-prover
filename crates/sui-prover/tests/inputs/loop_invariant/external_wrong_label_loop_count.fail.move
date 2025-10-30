module 0x42::loop_invariant_external_wrong_label_loop_count_fail;

use prover::prover::ensures;

#[spec_only(loop_inv(target = test_spec, label = 0u64))]
#[ext(no_abort)]
fun loop_inv(i: u64, n: u64, s: u128): bool {
    i <= n && (s == (i as u128) * ((i as u128) + 1) / 2)
}

#[spec(prove)]
fun test_spec(n: u64): u128 {
    let mut s: u128 = 0;
    let mut i = 0;

    while (i < n) {
        i = i + 1;
        s = s + (i as u128);
    };

    let mut j = 0;
    while (j < n) {
        j = j + 1;
        s = s + (j as u128);
    };

    ensures(s == (n as u128) * ((n as u128) + 1) / 2);
    s
}
