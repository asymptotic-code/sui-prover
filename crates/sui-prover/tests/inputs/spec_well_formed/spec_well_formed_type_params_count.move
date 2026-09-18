module 0x42::foo;

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

public fun foo<T>() {
  assert!(true);
}

#[mode(spec), ext(spec(prove))]
public fun foo_spec<T, K>() {
  foo<T>();
  ensures(true);
}
