module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

fun foo(x: &mut u8) {
    *x = 70;
}

fun bar(x: &mut u8) {
    foo(x);
}

#[spec(omit_opaque)]
fun foo_spec(x: &mut u8) {
    foo(x);
    *x = 0;
    ensures(x == 0);
}

#[spec(prove)]
fun bar_spec(x: &mut u8) {
    bar(x);

    ensures(x == 70); // ok
}