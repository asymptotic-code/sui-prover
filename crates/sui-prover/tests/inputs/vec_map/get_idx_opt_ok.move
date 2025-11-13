module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::vec_map;

fun foo(m: &mut vec_map::VecMap<u64, u8>) {
  m.insert(10, 0);
}

#[spec(prove)]
fun bar_spec(m: &mut vec_map::VecMap<u64, u8>) {
  requires(!m.contains(&10));
  foo(m);
  ensures(m.get(&10) == 0);
  ensures(m.get_idx_opt(&10) == option::some(0));
}
