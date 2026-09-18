module 0x42::ext_without_mode;

// #[ext(spec(...))] and #[ext(spec_only(...))] require #[mode(spec)].
#[ext(spec_only(axiom))]
fun helper(): bool {
    true
}

public fun foo(): u64 {
    1
}

#[ext(spec(prove))]
fun foo_spec(): u64 {
    let _ = helper();
    foo()
}
