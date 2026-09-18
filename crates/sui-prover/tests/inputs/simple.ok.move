module 0x42::foo;

public fun foo() {
  assert!(true);
}

#[mode(spec), ext(spec(prove))]
public fun foo_spec() {
  foo();
}
