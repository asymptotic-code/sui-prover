module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

public fun foo() {
  assert!(true);
}

#[mode(spec), ext(spec(prove))]
public fun foo_spec(x: u128) {
  foo();
  ensures(true);
}
