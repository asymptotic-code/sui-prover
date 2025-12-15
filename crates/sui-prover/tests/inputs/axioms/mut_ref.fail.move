module 0x42::simple_axiom;

use prover::prover::ensures;

#[spec_only(axiom)]
fun f_axiom(x: &mut u64): bool {
    *x > 4 && (*x).to_int().sqrt().gt(2u64.to_int())
}

public fun foo() {
  assert!(true);
}

#[spec(prove)]
public fun foo_spec() {
  foo();
  ensures(16u8.to_int().sqrt().gt(2u64.to_int()));
}
