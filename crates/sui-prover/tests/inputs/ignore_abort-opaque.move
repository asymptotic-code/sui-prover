module 0x42::foo;

fun foo(x: u64): u64 {
    bar(x)
}

fun bar(x: u64): u64 {
    x + 1
}

#[spec(prove)]
fun foo_spec(x: u64): u64 {
    foo(x)
}

#[spec(prove, ignore_abort)]
fun bar_spec(x: u64): u64 {
    bar(x)
}
