module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::vec_set;

fun foo(s: &mut vec_set::VecSet<u64>) {
  s.insert(10);
}

#[spec(prove)]
fun bar_spec(s: &mut vec_set::VecSet<u64>) {
  requires(!s.contains(&10));
  foo(s);
  ensures(s.contains(&10));
}
