module 0x42::foo;

use prover::prover::asserts;

fun bar(x: u8): u8 {
    assert(x != 0, 1);
    x
}

#[spec(prove)]
fun bar_spec(x: u8): u8 {
    asserts(x > 0);
    bar(x)
}

#[ext(no_abort)]
fun sna(x: u8): u8 {
    if (x == 0) {
        0
    } else {
        bar(x)
    }
}
