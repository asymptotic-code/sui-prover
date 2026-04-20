module 0x42::asserts_loop_early_break;

use prover::prover::{ensures, invariant, clone};

// Loop with early break that protects against abort. The body would
// underflow at `x - 1` if we hit `x == 0`, but the break exits before
// that. No function-level asserts is needed because the early break
// makes the function unconditionally non-aborting.
//
// The invariant must hold under both loop-exit paths (the natural
// `i == n` exit and the `break` exit). It also tracks `x <= *old_x`
// so the post-condition can pin down the result.

fun decrement_with_break(mut x: u64, n: u64): u64 {
    let old_x = clone!(&x);
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(x <= *old_x);
    });
    while (i < n) {
        if (x == 0) {
            break
        };
        x = x - 1;
        i = i + 1;
    };
    x
}

#[spec(prove)]
fun decrement_with_break_spec(x: u64, n: u64): u64 {
    let result = decrement_with_break(x, n);
    ensures(result <= x);
    result
}
