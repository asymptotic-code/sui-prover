module 0x42::simple_axiom;

use prover::prover::ensures;

#[ext(axiom), allow(unused_function)]
fun f_axiom(x: u64): bool {
    x.to_int().sqrt() == 3u8.to_int()
}

public fun foo() {
  assert!(true);
}

#[spec(prove)]
public fun foo_spec() {
  foo();
  ensures(16u8.to_int().sqrt() == 3u8.to_int());
}
