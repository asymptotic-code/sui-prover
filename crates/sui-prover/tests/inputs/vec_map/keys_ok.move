module 0x42::foo;

use prover::prover::ensures;

use sui::vec_map;

#[spec(prove)]
fun foo_spec(m: &vec_map::VecMap<u64, u8>) {
  ensures(m.keys().length() == m.length());
  ensures(m.keys().contains(&10) == m.contains(&10));
}
