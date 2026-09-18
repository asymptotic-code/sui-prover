module 0x42::foo;

use std::integer::Integer;
use prover::prover::ensures;

// Pure function that calls pow — its $pure body must use pow$pure
#[ext(pure)]
fun square(x: Integer): Integer {
    x.pow(2u8.to_int())
}

fun foo(x: Integer): Integer {
    square(x)
}

#[mode(spec), ext(spec(prove, uninterpreted = std::integer::pow))]
fun foo_spec(x: Integer): Integer {
    let result = foo(x);
    ensures(result == x.mul(x)); // fails: pow is uninterpreted inside square$pure
    result
}
