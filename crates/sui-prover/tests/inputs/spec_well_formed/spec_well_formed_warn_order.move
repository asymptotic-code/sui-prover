module 0x42::foo;

#[spec_only]
use prover::prover::asserts;

fun add(x: u64, _y: u64): u64 {
    x
}

#[spec(prove)]
fun add_spec(x: u64, _y: u64): u64 {
    let res = add(x, _y);
    asserts(true);
    res
}
