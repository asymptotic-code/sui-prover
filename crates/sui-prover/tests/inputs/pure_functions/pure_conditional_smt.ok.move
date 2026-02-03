/// Test that pure functions with conditionals work correctly through to SMT verification.
/// This test has a VALID pure function with branching logic, and the spec makes a
/// TRUE claim that the SMT solver can verify.
///
/// Expected: Should reach SMT verification and pass.
module 0x42::pure_conditional_smt_ok;

#[spec_only]
use prover::prover::ensures;

// Valid pure function with conditional - passes all syntactic checks:
// - No mutable references
// - Single return value
// - No aborts (subtraction is safe because x > 1 when we do x - 1)
// - Deterministic
// - Only calls other pure/allowed functions
#[ext(pure)]
fun decrement_or_zero(x: u64): u64 {
    if (x > 1) {
        x - 1
    } else {
        0
    }
}

public fun call_decrement_or_zero(x: u64): u64 {
    decrement_or_zero(x)
}

// This spec calls the pure function and makes a TRUE claim.
// The pure function is valid, so this should reach SMT verification and pass.
// decrement_or_zero(5) = 4, which is correct.
#[spec(prove)]
fun test_pure_conditional_spec(): u64 {
    let result = call_decrement_or_zero(5);
    // This is TRUE: decrement_or_zero(5) = 4
    ensures(result == 4);
    result
}
