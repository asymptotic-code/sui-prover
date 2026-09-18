module 0x42::foo;

use prover::prover::ensures;

public fun foo() {
  assert!(true);
}

#[mode(spec), ext(spec(prove, skip, focus))]
public fun foo_spec() {
  foo();
  ensures(true); 
}
