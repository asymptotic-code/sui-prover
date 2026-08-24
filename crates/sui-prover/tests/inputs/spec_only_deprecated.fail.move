module 0x42::spec_only_deprecated_test;

// #[spec_only] has been replaced by #[mode(spec)] and should produce an error
#[spec_only]
native fun helper(): u64;

public fun foo(): u64 {
    1
}

#[spec(prove)]
public fun foo_spec(): u64 {
    foo()
}
