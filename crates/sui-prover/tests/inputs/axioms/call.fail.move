module 0x42::simple_axiom;

use prover::prover::ensures;

#[spec_only(axiom)]
fun f_axiom(x: u64): bool {
  x.to_int().sqrt().gte(1u8.to_int())
}

public fun foo() {
  assert!(true);
  f_axiom(10);
}

#[spec(prove)]
public fun foo_spec() {
  foo();
  ensures(16u8.to_int().sqrt().gt(2u64.to_int()));
}
