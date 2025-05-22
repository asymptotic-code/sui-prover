module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

fun foo(x: &mut u8) {
    *x = 70;
}

fun bar(x: &mut u8) {
    foo(x);
}

#[spec(prove)]
fun foo_spec(x: &mut u8) {
    foo(x);
}

#[spec(prove)]
fun bar_spec(x: &mut u8) {
    bar(x);

    ensures(x == 70); // issue
}