module 0x42::fb {
  public fun bar() {
    assert!(true);
  }
}

module 0x42::bar_specs {
  use prover::prover::ensures;

  #[spec(prove, target = 0x42::missing_module::bar)]
  public fun bar_spec() {
    ensures(true);
  }
}

// Should fail with a meaningful error: the target's module does not exist.
