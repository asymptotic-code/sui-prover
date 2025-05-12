module 0x42::foo_tmp;

use sui::vec_map;
use prover::prover::{requires, ensures};

fun foo(m: &mut vec_map::VecMap<u64, u8>) {
    m.insert(10, 10);
}


#[spec(prove)]
fun foo_spec(m: &mut vec_map::VecMap<u64, u8>) {
  requires(!m.keys().contains(&10));
  foo(m);
  ensures(m.keys().contains(&10));
}