/// Test that void pure functions with early returns don't crash.
/// A void pure function is not useful (produces no value for the Boogie function),
/// so we expect a verification error rather than a panic.
module 0x42::pure_early_return_void;

#[ext(pure)]
fun do_nothing(x: u64) {
    if (x > 0) {
        return
    };
}

public fun call_do_nothing(x: u64) {
    do_nothing(x)
}
