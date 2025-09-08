module 0x42::opaque_tests;

use prover::prover::{ensures};

fun add_wrap(x: u64, y: u64): u64 {
    (((x as u128) + (y as u128)) % 18446744073709551616) as u64
}

#[spec(prove)]
fun add_wrap_spec(x: u64, y: u64): u64 {
    let result = add_wrap(x, y);
    ensures(result == x.to_int().add(y.to_int()).to_u64());
    result
}
