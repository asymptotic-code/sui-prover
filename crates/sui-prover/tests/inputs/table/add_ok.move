module 0x42::foo;

use prover::prover::{requires, ensures, clone};

use sui::table::Table;

fun foo(t: &mut Table<u64, u8>) {
  t.add(10, 0);
}

#[spec(prove)]
fun bar_spec(t: &mut Table<u64, u8>) {
  requires(!t.contains(10));
  let old_t = clone!(t);
  foo(t);
  requires(t.contains(10));
  ensures(t[10] == 0);
  ensures(!t.is_empty());
  ensures(t.length().to_int() == old_t.length().to_int().add(1u64.to_int()));
}
