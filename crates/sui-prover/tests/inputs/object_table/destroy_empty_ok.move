module 0x42::foo;

use prover::prover::requires;

use sui::object_table::ObjectTable;

public struct Foo has key, store {
  id: UID,
}

fun foo(t: ObjectTable<u64, Foo>) {
  t.destroy_empty()
}

#[spec(prove)]
fun foo_spec(t: ObjectTable<u64, Foo>) {
  requires(t.is_empty());
  foo(t);
}
