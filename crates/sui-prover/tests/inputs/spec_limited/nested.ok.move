module 0x42::foo;

#[spec_limited(abort_check)]
fun sum(x: u32, y: u32): u64 {
    (x as u64) + (y as u64)
}

#[spec_limited(abort_check)]
fun mul_sum(x: u32, y: u32): u128 {
    (((x as u64) * (y as u64)) + sum(x, y)) as u128
}
