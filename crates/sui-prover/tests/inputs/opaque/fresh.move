module 0x42::opaque_tests;

use prover::prover::{fresh};

#[spec_only]
fun fresh_with_type_withness<T, U>(_: &T): U {
    fresh()
}

#[spec(prove)]
fun fresh_with_type_withness_spec<T, U>(x: &T): U {
    fresh_with_type_withness(x)
}
