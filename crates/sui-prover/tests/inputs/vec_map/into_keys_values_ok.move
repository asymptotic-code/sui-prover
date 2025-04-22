module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::vec_map;

#[spec(prove)]
fun foo_spec(m: vec_map::VecMap<u64, u8>) {
  requires(m.contains(&10));
  requires(m[&10] == 0);
  let (keys, values) = m.into_keys_values();
  let (ok, idx) = keys.index_of(&10);
  ensures(ok);
  ensures(values[idx] == 0);
}

#[spec(prove)]
fun bar_spec(m: vec_map::VecMap<u64, u8>) {
  requires(!m.contains(&10));
  let (keys, _values) = m.into_keys_values();
  let (ok, _idx) = keys.index_of(&10);
  ensures(!ok);
}
