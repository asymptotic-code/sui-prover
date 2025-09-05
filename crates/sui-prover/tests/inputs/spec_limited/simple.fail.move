#[allow(unused_function)]
module 0x42::foo;

#[ext(no_abort)]
fun test_spec_limited_abort(x: u32, y: u32): u32 {
    (x * y) as u32
}
