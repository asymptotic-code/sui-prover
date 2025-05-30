module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_field;

public struct Foo has key {
    id: UID,
}

fun foo(x: &mut Foo) {
    *(dynamic_field::borrow_mut<u64, u8>(&mut x.id, 10)) = 0;
}

#[spec(prove)]
fun foo_spec(x: &mut Foo) {
    requires(dynamic_field::exists_with_type<u64, u8>(&x.id, 10));
    foo(x);
    ensures(dynamic_field::exists_with_type<u64, u8>(&x.id, 10));
    ensures(dynamic_field::borrow<u64, u8>(&x.id, 10) != 0);
}
