module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_field;

public struct Foo has key {
    id: UID,
}

fun foo(x: &mut Foo) {
    dynamic_field::add<u64, u64>(&mut x.id, 10u64, 0);
}

#[spec(prove)]
fun foo_spec(x: &mut Foo) {
    requires(!dynamic_field::exists_with_type<u64, u64>(&x.id, 10u64));
    foo(x);
    ensures(dynamic_field::exists_(&x.id, 10u64));
    ensures(dynamic_field::exists_with_type<u64, u64>(&x.id, 10u64));
    ensures(dynamic_field::borrow<u64, u64>(&x.id, 10) == 0);
}
