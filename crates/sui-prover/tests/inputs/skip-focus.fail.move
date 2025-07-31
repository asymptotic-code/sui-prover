module 0x42::foo;

use prover::prover::ensures;

public fun foo() {
  assert!(true);
}

#[spec(prove, skip, focus)]
public fun foo_spec() {
  foo();
  ensures(true); 
}
