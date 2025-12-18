module 0x42::foo;

use prover::prover::{requires, ensures, clone};

use sui::table::Table;

fun foo(t: &mut Table<u64, u8>): u8 {
  t.remove(10)
}

#[spec(prove)]
fun bar_spec(t: &mut Table<u64, u8>): u8 {
  requires(t.contains(10));
  requires(t[10] == 0);
  let old_t = clone!(t);
  let result = foo(t);
  ensures(!t.contains(10));
  ensures(result == 0);
  ensures(t.length().to_int() == old_t.length().to_int().sub(1u64.to_int()));
  result
}
