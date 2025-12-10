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

#[spec(prove)]
fun foo_spec(x: &mut Foo) {
    requires(dynamic_object_field::exists_with_type<u64, Bar>(&x.id, 10));
    foo(x);
    ensures(!dynamic_object_field::exists_with_type<u64, Bar>(&x.id, 10));
}
