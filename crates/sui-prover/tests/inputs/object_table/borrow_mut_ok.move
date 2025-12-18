module 0x42::foo;

use prover::prover::{requires, ensures, clone};

use sui::object_table::ObjectTable;

public struct Foo has key, store {
  id: UID,
  val: u8,
}

fun foo(t: &mut ObjectTable<u64, Foo>) {
  let foo_ref = &mut t[10];
  let val_ref = &mut foo_ref.val;
  *val_ref = 0;
}

#[spec(prove)]
fun bar_spec(t: &mut ObjectTable<u64, Foo>) {
  requires(t.contains(10));
  let old_t = clone!(t);
  foo(t);
  ensures(t.contains(10));
  ensures(&t[10].val == 0);
  ensures(t.length() == old_t.length());
}
