module 0x42::foo;

#[mode(spec)]
use prover::prover::ensures;

public fun foo(x: u128) {
  assert!(true);
}

#[spec(prove)]
public fun foo_spec(x: u128): u128 {
  foo(x);
  ensures(true);

  x
}
