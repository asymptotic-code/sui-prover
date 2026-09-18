#[spec_only, mode(spec), ext(spec_only)]
module 0x42::mixed_syntax;

// The deprecated attributes cannot be combined with the new syntax on one item.
#[spec_only, mode(spec), ext(spec_only)]
fun helper(): bool {
    true
}

#[spec_only(axiom), mode(spec), ext(spec_only(axiom))]
fun an_axiom(): bool {
    true
}

public fun foo(): u64 {
    1
}

#[spec(prove), mode(spec), ext(spec(prove))]
fun foo_spec(): u64 {
    foo()
}

// Mixing within one kind is an error too: old #[spec] with new ext(spec_only).
#[spec(prove), mode(spec), ext(spec_only)]
fun bar_spec(): u64 {
    foo()
}
