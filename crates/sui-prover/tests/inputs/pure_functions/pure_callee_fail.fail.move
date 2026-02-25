/// Test that pure functions cannot call non-pure functions that DON'T satisfy pure requirements.
/// The helper function aborts, so it cannot be used as a pure callee.
module 0x42::pure_callee_fail;

// This function aborts, violating pure requirements
fun checked_sub(x: u64, y: u64): u64 {
    assert!(x >= y, 0);
    x - y
}

// Pure function that tries to call an aborting function
#[ext(pure)]
fun bad_compute(x: u64, y: u64): u64 {
    checked_sub(x, y)
}
