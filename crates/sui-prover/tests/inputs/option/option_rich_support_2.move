#[allow(unused_function)]
module 0x42::working_test;

use prover::prover::{requires, ensures};
use std::option::some;

fun frob(x: u8, y: u8): Option<u8> {
    some(x+y)
}

#[spec(prove)]
fun frob_spec(x: u8, y: u8): Option<u8> {
    requires(x <= 100 && y <= 100 && 0 < y);
    let z = x+y;
    let r = frob(x, y);
    ensures(r == some(z));
    r
}
