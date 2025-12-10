module 0x42::foo;

use prover::prover::{requires, asserts};

use std::string::{Self, String};
use sui::dynamic_field;

public struct Foo has key {
    id: UID,
}

public fun borrow_uid(foo: &Foo): &UID {
    &foo.id
}

public fun foo(foo: &Foo): bool {
    *dynamic_field::borrow<String, u64>(&foo.id, string::utf8(b"asdf")) == 10
}

#[spec(prove)]
public fun foo_spec(foo: &Foo): bool {
    let id = borrow_uid(foo);
    requires(string::try_utf8(b"asdf").is_some());
    let asdf_key = string::utf8(b"asdf");
    asserts(dynamic_field::exists_with_type<String, u64>(id, asdf_key));
    foo(foo)
}
