module 0x42::ext_spec_requires_mode_test;

// #[ext(spec(...))] without #[mode(spec)] should produce an error
#[ext(spec(axiom))]
fun helper(): bool {
    true
}

public fun foo(): u64 {
    1
}

#[spec(prove)]
public fun foo_spec(): u64 {
    let _ = helper();
    foo()
}
