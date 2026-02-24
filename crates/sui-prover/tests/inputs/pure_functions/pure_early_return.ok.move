/// Test that pure functions with early returns work correctly.
/// The early return should not be dropped during pure function translation.
module 0x42::pure_early_return;

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

#[spec(prove)]
fun test_is_positive(): bool {
    let result = check_positive(5);
    ensures(result == true);
    result
}
