/// Test that pure functions can have multiple return values.
/// This aligns pure functions with opaque functions, which already support
/// any number of return values.
///
/// Expected: Should pass verification.
module 0x42::pure_multiple_returns;

#[spec_only]
use prover::prover::ensures;

// Pure function with 2 return values
#[ext(pure)]
fun swap(x: u64, y: u64): (u64, u64) {
    (y, x)
}

// Pure function with 3 return values
#[ext(pure)]
fun triple(x: u64): (u64, u64, u64) {
    (x, x + 1, x + 2)
}

public fun call_swap(x: u64, y: u64): (u64, u64) {
    swap(x, y)
}

public fun call_triple(x: u64): (u64, u64, u64) {
    triple(x)
}

// Verify swap function works correctly
#[spec(prove)]
fun test_swap_spec(): (u64, u64) {
    let (a, b) = call_swap(5, 10);
    // swap(5, 10) should return (10, 5)
    ensures(a == 10);
    ensures(b == 5);
    (a, b)
}

// Verify triple function works correctly
#[spec(prove)]
fun test_triple_spec(): (u64, u64, u64) {
    let (x, y, z) = call_triple(7);
    // triple(7) should return (7, 8, 9)
    ensures(x == 7);
    ensures(y == 8);
    ensures(z == 9);
    (x, y, z)
}
