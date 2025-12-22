module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

#[ext(pure)]
public fun bar_impl(x: u64): u64 {
    let mut y: u64 = x - x + x;
    let z: u64 = if (x < 10) {
        y = x + 10;
        x
    } else {
        y - 1
    };
    y - z
}

public fun bar(x: u64): u64 {
    bar_impl(x)
}

#[spec(prove)]
fun bar_spec(x: u64): u64 {
    let result = bar(x);
    ensures(result >= x); // WRONG: should be >= 1
    ensures(result <= 10);
    result
}
