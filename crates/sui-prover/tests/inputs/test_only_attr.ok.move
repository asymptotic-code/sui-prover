#[allow(unused_function)]
module 0x42::working_test;

use sui::test_utils::destroy; // check test imports

#[mode(spec), ext(spec_only)]
use prover::prover::{asserts, requires, ensures};

#[test_only] // check test_only attribute visibility
fun foo(x: u8, y: u8): u16 {
    (x as u16) + (y as u16)
}

#[mode(spec), ext(spec(prove))]
fun foo_spec(x: u8, y: u8): u16 {
    requires(x <= 50 && y <= 50);
    let r = foo(x, y);
    ensures(r <= 100);
    r
}
