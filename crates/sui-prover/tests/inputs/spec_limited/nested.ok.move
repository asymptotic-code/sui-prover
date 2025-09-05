#[allow(unused_function)]
module 0x42::foo;

#[ext(no_abort)]
fun sum(x: u32, y: u32): u64 {
    (x as u64) + (y as u64)
}

#[ext(no_abort)]
fun mul_sum(x: u32, y: u32): u128 {
    (((x as u64) * (y as u64)) + sum(x, y)) as u128
}
