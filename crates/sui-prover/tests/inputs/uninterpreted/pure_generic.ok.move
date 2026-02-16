module 0x42::foo;

use prover::prover::ensures;

/// Generic pure function called with concrete type args.
/// Tests that type-instantiated $pure declarations are emitted
/// even when the function body is available.
#[ext(pure)]
fun contains<K: copy + drop, V: drop>(k: K, _v: V): bool {
    let _unused = k;
    false
}

fun foo(k: u64, v: u8): bool {
    contains(k, v)
}

#[spec(prove, uninterpreted = contains)]
fun foo_spec(k: u64, v: u8): bool {
    let result = foo(k, v);
    ensures(result == contains(k, v));
    result
}
