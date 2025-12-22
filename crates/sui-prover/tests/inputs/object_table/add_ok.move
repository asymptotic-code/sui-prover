module 0x42::foo;

use prover::prover::{requires, ensures, clone};

use sui::object_table::ObjectTable;

public struct Foo has key, store {
  id: UID,
}

fun foo(t: &mut ObjectTable<u64, Foo>, v: Foo) {
  t.add(10, v);
}

#[spec(prove)]
fun bar_spec(t: &mut ObjectTable<u64, Foo>, v: Foo) {
  requires(!t.contains(10));
  let old_t = clone!(t);
  let old_v = clone!(&v);
  foo(t, v);
  requires(t.contains(10));
  ensures(&t[10] == old_v);
  ensures(!t.is_empty());
  ensures(t.length().to_int() == old_t.length().to_int().add(1u64.to_int()));
}
