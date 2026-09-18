module 0x42::spec_and_spec_only;

public fun foo(): u64 {
    1
}

// An item is either a spec or spec-only code, not both.
#[mode(spec), ext(spec(prove), spec_only)]
fun foo_spec(): u64 {
    foo()
}
