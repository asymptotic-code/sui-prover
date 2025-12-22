module 0x42::foo;

use prover::prover::{ensures, clone};

use sui::vec_set;

fun foo(s: vec_set::VecSet<u64>): vec_set::VecSet<u64> {
    vec_set::from_keys(s.into_keys())
}

#[spec(prove)]
fun foo_spec(s: vec_set::VecSet<u64>): vec_set::VecSet<u64> {
  let old_s = clone!(&s);
  let result = foo(s);
  ensures(&result == old_s);
  result
}
