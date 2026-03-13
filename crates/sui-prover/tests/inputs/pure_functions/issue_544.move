/// Regression test for https://github.com/asymptotic-code/sui-prover/issues/544
/// Panic: "unexpected 0 destinations for operation TraceLocal(0) in function table_is_good"
///
/// Root cause: when a non-pure function is called by a #[ext(pure)] function,
/// it becomes a "pure callee" and is translated with FunctionTranslationStyle::Pure.
/// The Pure arm in the bytecode builder did not filter out TraceLocal operations
/// (which have 0 destinations), so generate_pure_expression panicked when it
/// encountered them in the Call handler expecting exactly 1 destination.
module 0x42::issue_544;

use prover::prover::{ensures, forall};

// Pure predicate function called from within the quantifier
#[ext(pure)]
fun is_at_least(x: &u64, bound: u64): bool {
    *x >= bound
}

// A non-pure function that uses forall! (not marked #[ext(pure)])
// This becomes a "pure callee" when called from is_valid_bound.
fun all_values_at_least(bound: u64): bool {
    forall!<u64>(|x| is_at_least(x, bound))
}

// A pure function that calls the non-pure function (making it a "pure callee").
// When this is marked #[ext(pure)], the non-pure callee gets translated with
// FunctionTranslationStyle::Pure, which previously panicked on TraceLocal ops
// (with debug_trace=true, which is the default for CLI usage).
#[ext(pure)]
fun is_valid_bound(lower: u64, upper: u64): bool {
    all_values_at_least(lower) && upper >= lower
}

public fun check_bound(lower: u64, upper: u64): bool {
    is_valid_bound(lower, upper)
}

#[spec(prove)]
fun test_check_bound() {
    let result = check_bound(0, 100);
    ensures(result);
}
