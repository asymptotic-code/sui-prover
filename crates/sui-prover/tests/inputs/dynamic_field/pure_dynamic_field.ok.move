module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_field;

public struct Foo has key {
    id: UID,
}

#[ext(pure)]
fun has_field(x: &Foo): bool {
    dynamic_field::exists_with_type<u64, u8>(&x.id, 10)
}

fun foo(x: &mut Foo) {
    dynamic_field::add<u64, u8>(&mut x.id, 10, 42);
}

#[spec(prove)]
fun foo_spec(x: &mut Foo) {
    requires(!dynamic_field::exists_with_type<u64, u8>(&x.id, 10));
    foo(x);
    ensures(has_field(x));
}