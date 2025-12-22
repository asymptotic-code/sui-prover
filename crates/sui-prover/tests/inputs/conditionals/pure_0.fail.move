module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

#[ext(pure)]
fun foo_impl(x: u64): u64 {
    let mut y: u64 = x - x + x;
    if (y < 10) {
        y = y + 1;
    };
    y
}

public fun foo(x: u64): u64 {
    foo_impl(x)
}

#[spec(prove)]
fun foo_spec(x: u64): u64 {
    let result = foo(x);
    ensures(result >= 1);
    ensures(result <= x); // WRONG: should be >= x
    result
}
