module 0x42::fb {
  native fun foo();

  public fun bar() {
    foo();
    assert!(true);
  }
}

module 0x42::foo_specs {
  use prover::prover::ensures;
  use 0x42::fb::foo;

  #[spec(prove, target = 0x42::fb::foo)]
  public fun foo_spec() {
    foo();
    ensures(true); 
  }
}

module 0x42::bar_specs_double_foo_imported_module {
  use prover::prover::ensures;
  use 0x42::fb::bar;

  #[spec(prove, target = 0x42::fb::bar, include = 0x42::foo_specs::foo_spec)]
  public fun bar_spec() {
    bar();
    ensures(true); 
  }
}
// Should not fail because we include foo_spec which saves us from using unimplemented native foo
