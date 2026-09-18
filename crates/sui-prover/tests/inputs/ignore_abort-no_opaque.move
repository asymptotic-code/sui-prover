module 0x42::foo;

fun foo(x: u64): u64 {
    bar(x)
}

fun bar(x: u64): u64 {
    x + 1
}

#[mode(spec), ext(spec(prove))]
fun foo_spec(x: u64): u64 {
    foo(x)
}

#[mode(spec), ext(spec(prove, ignore_abort, no_opaque))]
fun bar_spec(x: u64): u64 {
    bar(x)
}
