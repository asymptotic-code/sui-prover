module 0x42::foo;

#[spec_limited(abort_check)]
fun test_spec_limited_abort(x: u32, y: u32): u32 {
    (x * y) as u32
}
