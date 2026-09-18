#[allow(deprecated_usage)]
module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_object_field;

public struct Foo has key {
    id: UID,
}

public struct Bar has key, store {
    id: UID,
    bar: u64,
}

fun foo(x: &mut Foo) {
    dynamic_object_field::borrow_mut<u64, Bar>(&mut x.id, 10).bar = 0;
}

#[mode(spec), ext(spec(prove))]
fun foo_spec(x: &mut Foo) {
    requires(dynamic_object_field::exists_with_type<u64, Bar>(&x.id, 10));
    foo(x);
    ensures(dynamic_object_field::exists(&x.id, 10u64));
    // the deprecated `exists_` wrapper agrees with the renamed `exists`
    ensures(
        dynamic_object_field::exists(&x.id, 10u64) == dynamic_object_field::exists_(&x.id, 10u64),
    );
    ensures(dynamic_object_field::exists_with_type<u64, Bar>(&x.id, 10));
    ensures(dynamic_object_field::borrow<u64, Bar>(&x.id, 10).bar == 0);
}

fun has_bar(x: &Foo): bool {
    dynamic_object_field::exists(&x.id, 10u64)
}

#[mode(spec), ext(spec(prove))]
fun has_bar_spec(x: &Foo): bool {
    requires(dynamic_object_field::exists_with_type<u64, Bar>(&x.id, 10));
    let res = has_bar(x);
    ensures(res);
    res
}
