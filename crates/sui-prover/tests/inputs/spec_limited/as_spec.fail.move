module 0x42::foo;

#[spec_only]
use prover::prover::ensures;

#[spec_limited(abort_check)]
fun sum(x: u32, y: u32): u64 {
    (x as u64) + (y as u64)
}

#[spec(prove)]
fun sum_spec(x: u32, y: u32): u64 {
    let r = sum(x, y);
    ensures(r == (x as u64) + (y as u64));
    r
}
