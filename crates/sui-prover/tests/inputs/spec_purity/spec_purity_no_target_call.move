module 0x42::foo;

public fun foo() {}

#[spec(prove)]
public fun foo_spec() {
    assert!(true);
}
