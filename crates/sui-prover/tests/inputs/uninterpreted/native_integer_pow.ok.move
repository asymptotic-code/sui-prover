module 0x42::foo;

use std::integer::Integer;
use prover::prover::ensures;

fun foo(a: Integer, b: Integer): Integer {
    a.pow(b)
}

#[spec(prove, uninterpreted = std::integer::pow)]
fun foo_spec(a: Integer, b: Integer): Integer {
    let result = foo(a, b);
    ensures(result == result);
    result
}
