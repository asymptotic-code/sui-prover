module 0x42::foo;

#[spec_only]
use prover::prover::{requires, ensures};

public fun add_up(x: u8, y: u8): u8 {
    let r = x + y;
    r
}

#[spec(prove)]
fun add_up_spec(x: u8, y: u8): u8 {
    requires(x <= 127);
    let r = add_up(x, x); // <=== wrong call - should be add_up(x, y)
    ensures(r.to_int() == x.to_int().add(x.to_int()));
    r
}

fun add_up_caller(x: u8): u8 {
    add_up(1, x)
}

#[spec(prove)]
fun add_up_caller_spec(x: u8): u8 {
    let r = add_up_caller(x);
    ensures(r == 2); // <== should not be provable, but it is
    r
} 