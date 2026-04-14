/// Test that pure functions with early returns verify correctly (negative test).
/// This spec makes a FALSE claim to verify the early return is not dropped.
module 0x42::pure_early_return_fail;

#[spec_only]
use prover::prover::ensures;

#[ext(pure)]
fun is_positive(x: u64): bool {
    if (x > 0) {
        return true
    };
    false
}

public fun check_positive(x: u64): bool {
    is_positive(x)
}

// This spec makes a FALSE claim: is_positive(5) should be true, not false.
#[spec(prove)]
fun test_is_positive_wrong(): bool {
    let result = check_positive(5);
    ensures(result == false);
    result
}
