module 0x42::mode_without_ext;

// #[mode(spec)] requires #[ext(spec(...))] or #[ext(spec_only(...))].
#[mode(spec)]
fun helper(): bool {
    true
}

// ...also with an unrelated ext attribute.
#[mode(spec), ext(pure)]
fun pure_helper(): bool {
    true
}

public fun foo(): u64 {
    1
}

#[mode(spec), ext(spec(prove))]
fun foo_spec(): u64 {
    foo()
}
