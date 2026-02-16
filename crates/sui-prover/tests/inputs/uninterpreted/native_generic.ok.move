module 0x42::foo;

use prover::prover::ensures;

#[ext(pure)]
#[spec_only]
native fun bar<T1, T2>(x: u64): u64;

fun foo(x: u64): u64 {
    bar<u8, u16>(x)
}

/// Calling an uninterpreted generic native with concrete type args should
/// produce matching declaration and call-site names in Boogie.
#[spec(prove, uninterpreted = bar)]
fun foo_spec(x: u64): u64 {
    let result = foo(x);
    ensures(result == bar<u8, u16>(x));
    result
}
