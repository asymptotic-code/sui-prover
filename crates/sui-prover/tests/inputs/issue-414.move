module 0x42::foo;

public fun foo(x: u64) {
    if (x > 0) {}
}

#[spec(prove)]
fun foo_spec(x: u64) {
    foo(x);
}

public fun bar(x: u64) {
    if (x > 0) {} else {}
}

#[spec(prove)]
fun bar_spec(x: u64) {
    bar(x);
}
