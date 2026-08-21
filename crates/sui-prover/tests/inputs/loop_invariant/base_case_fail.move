/// Test that a loop invariant failing on loop entry shows
/// "loop invariant does not hold on loop entry" in the error.
module 0x42::base_case_fail;

use prover::prover::ensures;

#[mode(spec), ext(spec(loop_inv(target = foo_spec)), no_abort)]
#[allow(unused_function)]
fun loop_inv_0(i: u64, n: u64): bool {
    // This invariant is wrong at entry: i starts at 0, but we claim i > 0.
    i > 0 && i <= n
}

#[spec(prove)]
fun foo_spec(n: u64): u64 {
    let mut i = 0;
    while (i < n) {
        i = i + 1;
    };
    ensures(i == n);
    i
}
