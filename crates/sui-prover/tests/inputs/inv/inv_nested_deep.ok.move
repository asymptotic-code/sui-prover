module 0x42::inv_nested_deep;

public struct Inner has copy, drop {
    x: u64
}

public struct Outer has copy, drop {
    inner: Inner,
    y: u64,
}

#[spec_only]
public fun Inner_inv(s: &Inner): bool {
    s.x > 0
}

#[spec_only]
public fun Outer_inv(s: &Outer): bool {
    s.y > 0
}

// Both Outer_inv and Inner_inv should be checked.
// Outer { inner: Inner { x: 1 }, y: 0 } satisfies Inner_inv but violates Outer_inv.
public fun make_bad_outer(): Outer {
    Outer { inner: Inner { x: 1 }, y: 0 }
}

// Outer { inner: Inner { x: 0 }, y: 1 } violates Inner_inv but satisfies Outer_inv.
public fun make_bad_inner(): Outer {
    Outer { inner: Inner { x: 0 }, y: 1 }
}

// Both invariants satisfied.
public fun make_good(): Outer {
    Outer { inner: Inner { x: 1 }, y: 1 }
}

#[spec(prove)]
fun make_bad_outer_spec(): Outer {
    make_bad_outer()
}

#[spec(prove)]
fun make_bad_inner_spec(): Outer {
    make_bad_inner()
}

#[spec(prove)]
fun make_good_spec(): Outer {
    make_good()
}
