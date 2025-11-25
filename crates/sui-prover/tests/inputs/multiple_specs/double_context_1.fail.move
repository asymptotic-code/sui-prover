module 0x42::fb {
  public fun foo() {
    assert!(true);
  }

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

#[spec_only(include = 0x42::foo_specs)]
module 0x42::bar_specs_double_foo_imported_module {
  use prover::prover::ensures;
  use 0x42::fb::{foo, bar};

  #[spec(prove, target = 0x42::fb::foo)]
  public fun foo_spec() {
    foo();
    ensures(true); 
  }

  #[spec(prove, target = 0x42::fb::bar)]
  public fun bar_spec() {
    bar();
    ensures(true); 
  }
}

// Should FAIL because of duplicate spec for foo in same context
