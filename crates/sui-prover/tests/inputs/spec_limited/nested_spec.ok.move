#[allow(unused_function)]
module 0x42::foo;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
fun sum(x: u32, y: u32): u64 {
    (x as u64) + (y as u64)
}

#[spec(prove)]
fun sum_spec(x: u32, y: u32): u64 {
    let r = sum(x, y);
    ensures(r == (x as u64) + (y as u64));
    r
}

#[ext(no_abort)]
fun mul_sum(x: u32, y: u32): u128 {
    (((x as u64) * (y as u64)) + sum(x, y)) as u128
}
