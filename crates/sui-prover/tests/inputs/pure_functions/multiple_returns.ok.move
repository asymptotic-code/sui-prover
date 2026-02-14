/// Test that pure functions work correctly with various arithmetic operations.
///
/// Expected: Should pass verification.
module 0x42::pure_multiple_returns;

#[spec_only]
use prover::prover::ensures;

// Pure function that adds two numbers
#[ext(pure)]
fun add(x: u64, y: u64): u64 {
    x + y
}

// Pure function that multiplies and adds
#[ext(pure)]
fun compute(x: u64, y: u64): u64 {
    x * 2 + y
}

public fun call_add(x: u64, y: u64): u64 {
    add(x, y)
}

public fun call_compute(x: u64, y: u64): u64 {
    compute(x, y)
}

// Verify add function works correctly
#[spec(prove)]
fun test_add_spec(): u64 {
    let result = call_add(5, 10);
    // add(5, 10) should return 15
    ensures(result == 15);
    result
}

// Verify compute function works correctly
#[spec(prove)]
fun test_compute_spec(): u64 {
    let result = call_compute(7, 3);
    // compute(7, 3) should return 7*2 + 3 = 17
    ensures(result == 17);
    result
}
