/// Test that pure functions work correctly through to SMT verification.
/// This test has a VALID pure function (passes all syntactic checks), but the
/// spec makes a false logical claim that can only be caught by the SMT solver.
///
/// Expected: Should reach SMT verification and fail there (not at bytecode transformation).
module 0x42::pure_smt_verification;

#[spec_only]
use prover::prover::ensures;

// Valid pure function - passes all syntactic checks:
// - No mutable references
// - Single return value
// - No aborts (uses subtraction to avoid overflow)
// - Deterministic
// - Only calls other pure/allowed functions
#[ext(pure)]
fun identity(x: u64): u64 {
    // x - x + x = 0 + x = x (no overflow possible)
    x - x + x
}

public fun call_identity(x: u64): u64 {
    identity(x)
}

// This spec calls the pure function and makes a FALSE claim.
// The pure function is valid, so this should reach SMT verification.
// The SMT solver should catch that identity(5) = 5, not 6.
#[spec(prove)]
fun test_pure_call_spec(): u64 {
    let result = call_identity(5);
    // This is FALSE: identity(5) = 5, not 6
    ensures(result == 6);
    result
}
