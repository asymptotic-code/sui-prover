/// Test that pure functions can call non-pure functions that satisfy pure requirements.
/// The helper function is NOT marked #[ext(pure)] but satisfies all pure requirements.
module 0x42::pure_callee_ok;

#[spec_only]
use prover::prover::ensures;

// This function is NOT marked #[ext(pure)] but satisfies pure requirements:
// - No mutable references
// - No aborts
// - Deterministic
fun add_one(x: u64): u64 {
    x + 1
}

// Another non-pure helper with conditional logic
fun max_val(a: u64, b: u64): u64 {
    if (a > b) { a } else { b }
}

// Transitive: calls another pure callee
fun add_two(x: u64): u64 {
    add_one(add_one(x))
}

// Pure function that calls non-pure helpers
#[ext(pure)]
fun compute(x: u64, y: u64): u64 {
    if (x <= 0xFFFFFFFFFFFFFFFD) {
        max_val(add_two(x), y)
    } else {
        y
    }
}

public fun call_compute(x: u64, y: u64): u64 {
    compute(x, y)
}

#[spec(prove)]
fun test_compute_spec(): u64 {
    let result = call_compute(3, 4);
    // add_two(3) = 5, max_val(5, 4) = 5
    ensures(result == 5);
    result
}
