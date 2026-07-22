module 0x42::fb {
  public fun bar() {
    assert!(true);
  }
}

module 0x42::bar_specs {
  use prover::prover::ensures;
  use 0x42::fb::bar;

  #[spec(prove, target = 0x42::fb::bar, include = 0x42::missing_specs::foo_spec)]
  public fun bar_spec() {
    bar();
    ensures(true);
  }
}

// Should fail with a meaningful error: the included spec's module does not exist.
