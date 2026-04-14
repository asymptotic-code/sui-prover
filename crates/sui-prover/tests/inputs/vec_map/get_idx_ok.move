module 0x42::foo;

use prover::prover::{requires, ensures, clone};

use sui::vec_map;

fun foo(m: &mut vec_map::VecMap<u64, u8>) {
  m.insert(10, 0);
}

#[spec(prove)]
fun bar_spec(m: &mut vec_map::VecMap<u64, u8>) {
  requires(!m.contains(&10));
  let old_m = clone!(m);
  foo(m);
  ensures(m.get_idx(&10) == old_m.length());
}

