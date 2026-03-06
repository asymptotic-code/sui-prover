module 0x42::pure_df_exists;

use prover::prover::{requires, ensures};

use sui::dynamic_field;

public struct Foo has key {
    id: UID,
}

#[ext(pure)]
fun has_field(foo: &Foo): bool {
    dynamic_field::exists_with_type<u64, u8>(&foo.id, 10)
}

#[spec(prove)]
fun has_field_spec(foo: &Foo): bool {
    requires(dynamic_field::exists_with_type<u64, u8>(&foo.id, 10));
    let r = has_field(foo);
    ensures(r);
    r
}
