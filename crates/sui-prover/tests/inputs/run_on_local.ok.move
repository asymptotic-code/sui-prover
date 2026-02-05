module 0x42::run_on_test;

public fun foo() {
    assert!(true);
}

// This spec should be able to run locally even when --cloud is configured
#[spec(prove, run_on="local")]
public fun foo_spec_local() {
    foo();
}

// This spec should run according to the global setting
#[spec(prove)]
public fun foo_spec_default() {
    foo();
}
