#[allow(deprecated_usage)]
module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_field;

public struct Foo has key {
    id: UID,
}

fun foo(x: &mut Foo) {
    dynamic_field::add<u64, u64>(&mut x.id, 10u64, 0);
}

#[mode(spec), ext(spec(prove))]
fun foo_spec(x: &mut Foo) {
    requires(!dynamic_field::exists_with_type<u64, u64>(&x.id, 10u64));
    foo(x);
    ensures(dynamic_field::exists(&x.id, 10u64));
    // the deprecated `exists_` wrapper agrees with the renamed `exists`
    ensures(dynamic_field::exists(&x.id, 10u64) == dynamic_field::exists_(&x.id, 10u64));
    ensures(dynamic_field::exists_with_type<u64, u64>(&x.id, 10u64));
    ensures(dynamic_field::borrow<u64, u64>(&x.id, 10) == 0);
}

fun add_if_missing(x: &mut Foo) {
    if (!dynamic_field::exists(&x.id, 7u64)) {
        dynamic_field::add<u64, u8>(&mut x.id, 7u64, 1);
    }
}

#[mode(spec), ext(spec(prove))]
fun add_if_missing_spec(x: &mut Foo) {
    requires(!dynamic_field::exists(&x.id, 7u64));
    add_if_missing(x);
    ensures(dynamic_field::exists_with_type<u64, u8>(&x.id, 7u64));
    ensures(dynamic_field::borrow<u64, u8>(&x.id, 7u64) == 1);
}
