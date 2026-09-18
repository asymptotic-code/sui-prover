module 0x42::run_on_invalid_test;

public fun foo() {
    assert!(true);
}

// This spec should fail, --cloud is not configured
#[mode(spec), ext(spec(prove, run_on=b"cloud"))]
public fun foo_spec_cloud() {
    foo();
}
