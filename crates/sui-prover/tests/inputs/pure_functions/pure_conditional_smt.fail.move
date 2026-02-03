/// Test that pure functions with conditionals work correctly through to SMT verification.
/// This test has a pure function with a BUG in its implementation (x - 10 instead of x - 1),
/// and the spec makes a claim that would be true for the correct implementation.
/// The SMT solver should catch that the buggy implementation doesn't satisfy the spec.
///
/// Expected: Should reach SMT verification and fail there (not at bytecode transformation).
module 0x42::pure_conditional_smt;

#[spec_only]
use prover::prover::{ensures, requires};

// BUGGY pure function - has x - 10 instead of x - 1
#[ext(pure)]
fun decrement_or_zero(x: u64): u64 {
    if (x > 1) {
        x - 10  // BUG: should be x - 1
    } else {
        0
    }
}

public fun call_decrement_or_zero(x: u64): u64 {
    decrement_or_zero(x)
}

// This spec makes a claim that would be TRUE for correct implementation
// but is FALSE for the buggy one.
// Require x > 10 to avoid underflow in the buggy implementation.
#[spec(prove)]
fun test_pure_conditional_spec(x: u64): u64 {
    requires(x > 10);
    let result = call_decrement_or_zero(x);
    // This would be TRUE for correct impl (x - 1 >= x - 1)
    // but is FALSE for buggy impl (x - 10 >= x - 1 is false when x > 10)
    ensures(result >= x - 1);
    result
}
