module 0x42::foo;

#[ext(pure)]
fun sub1(x: u8): u8 {
    if (x > 0) x - 1 else 0
}

fun apply() {
    assert!(sub1(1) <= 255, 1);
}

#[mode(spec), ext(spec(prove, uninterpreted = sub1))]
fun apply_spec() {
    apply()
}
