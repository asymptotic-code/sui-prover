module 0x42::foo;

use prover::prover::{ensures, clone};

use sui::vec_map;

fun foo(m: vec_map::VecMap<u64, u8>): vec_map::VecMap<u64, u8> {
  let (keys, values) = m.into_keys_values();
  vec_map::from_keys_values(keys, values)
}

#[spec(prove)]
fun foo_spec(m: vec_map::VecMap<u64, u8>): vec_map::VecMap<u64, u8> {
  let old_m = clone!(&m);
  let result = foo(m);
  ensures(&result == old_m);
  result
}
