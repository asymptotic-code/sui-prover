module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

public fun foo(x: u128): u128 {
  assert!(true);
  0u128
}

#[mode(spec), ext(spec(prove))]
public fun foo_spec(x: u128): u64 {
  foo(x);
  ensures(true);

  5u64
}
