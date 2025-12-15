module 0x42::simple_axiom;

use prover::prover::ensures;
use std::integer::Integer;

#[spec_only(axiom)]
fun f_axiom(x: u64): Integer {
    x.to_int().sqrt()
}

public fun foo() {
  assert!(true);
}

#[spec(prove)]
public fun foo_spec() {
  foo();
  ensures(16u8.to_int().sqrt().gt(2u64.to_int()));
}
