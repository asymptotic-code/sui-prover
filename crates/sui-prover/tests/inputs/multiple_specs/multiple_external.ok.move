module 0x42::fb {
  native fun foo();

  native fun bar();

  public fun foobar() {
    foo();
    assert!(true);
    bar();
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

module 0x42::bar_specs {
  use prover::prover::ensures;
  use 0x42::fb::bar;

  #[spec(prove, target = 0x42::fb::bar)]
  public fun bar_spec() {
    bar();
    ensures(true); 
  }
}

#[spec_only(include = 0x42::foo_specs, include = 0x42::bar_specs)]
module 0x42::foobar_specs_1 {
  use prover::prover::ensures;
  use 0x42::fb::foobar;

  #[spec(prove, target = 0x42::fb::foobar)]
  public fun foobar_spec() {
    foobar();
    ensures(true); 
  }
}

#[spec_only(include = 0x42::foo_specs::foo_spec, include = 0x42::bar_specs::bar_spec)]
module 0x42::foobar_specs_2 {
  use prover::prover::ensures;
  use 0x42::fb::foobar;

  #[spec(prove, target = 0x42::fb::foobar)]
  public fun foobar_spec() {
    foobar();
    ensures(true); 
  }
}

// Should not fail because we include foo_spec and bar_spec which saves us from using unimplemented native foo and bar