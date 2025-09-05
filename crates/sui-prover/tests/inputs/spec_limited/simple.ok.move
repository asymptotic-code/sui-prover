#[allow(unused_function)]
module 0x42::foo;

#[ext(no_abort)]
fun test_spec_limited_2(x: u32, y: u32): bool {
    x > y
}
