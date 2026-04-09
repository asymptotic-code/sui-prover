/// Test that nested early returns in pure functions work correctly.
/// When the outer condition is true but the inner is false, control
/// should fall through to the default return value.
module 0x42::pure_early_return_nested;

#[spec_only]
use prover::prover::ensures;

#[ext(pure)]
fun both_positive(x: u64, y: u64): bool {
    if (x > 0) {
        if (y > 0) {
            return true
        };
    };
    false
}

public fun call_both_positive(x: u64, y: u64): bool {
    both_positive(x, y)
}

#[spec(prove)]
fun test_tt(): bool {
    let r = call_both_positive(5, 3);
    ensures(r == true);
    r
}

#[spec(prove)]
fun test_tf(): bool {
    let r = call_both_positive(5, 0);
    ensures(r == false);
    r
}

#[spec(prove)]
fun test_ff(): bool {
    let r = call_both_positive(0, 0);
    ensures(r == false);
    r
}
