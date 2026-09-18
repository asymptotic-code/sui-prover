module 0x42::opaque_tests;

use prover::prover::{fresh};

#[mode(spec), ext(spec_only)]
fun fresh_with_type_withness<T, U>(_: &T): U {
    fresh()
}

#[mode(spec), ext(spec(prove))]
fun fresh_with_type_withness_spec<T, U>(x: &T): U {
    fresh_with_type_withness(x)
}
