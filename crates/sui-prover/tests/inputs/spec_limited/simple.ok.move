module 0x42::foo;

#[spec_limited(abort_check)]
fun test_spec_limited_ok(x: u32, y: u32): bool {
    x > y
}
