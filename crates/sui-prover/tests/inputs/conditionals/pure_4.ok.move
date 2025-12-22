module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

#[ext(pure)]
public fun foobar_impl(x: u64): u64 {
    let mut y: u64 = x - x + x;
    let z: u64 = if (x < 10) {
        y = x + 10;
        x
    } else {
        if (y > 5) {
            y = y - 1;
            y - 1
        } else {
            y = y + 1;
            y - 1
        }
    };
    y - z
}

public fun foobar(x: u64): u64 {
    foobar_impl(x)
}

#[spec(prove)]
fun foobar_spec(x: u64): u64 {
    let result = foobar(x);
    ensures(result <= 10);
    result
}
