module 0x42::foo;

#[mode(spec)]
use prover::prover::ensures;

public fun foo() {
  assert!(true);
}

#[spec(prove)]
public fun foo_failing_spec() {
  foo();
  ensures(false);
}
