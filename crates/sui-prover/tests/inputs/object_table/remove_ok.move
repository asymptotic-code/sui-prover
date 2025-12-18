module 0x42::foo;

use prover::prover::{requires, ensures, clone};

use sui::object_table::ObjectTable;

public struct Foo has key, store {
  id: UID,
}

fun foo(t: &mut ObjectTable<u64, Foo>): Foo {
  t.remove(10)
}

#[spec(prove)]
fun bar_spec(t: &mut ObjectTable<u64, Foo>): Foo {
  requires(t.contains(10));
  let old_t = clone!(t);
  let result = foo(t);
  ensures(!t.contains(10));
  ensures(result == &old_t[10]);
  ensures(t.length().to_int() == old_t.length().to_int().sub(1u64.to_int()));
  result
}
