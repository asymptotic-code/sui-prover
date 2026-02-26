module 0x42::inv_nested_field;

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

public fun make_bad_outer(): Outer {
    Outer { inner: Inner { x: 0 }, y: 1 }
}

// make_bad_outer has ensures checking Inner_inv on the nested Inner field.
// Inner { x: 0 } violates x > 0.
#[spec(prove)]
fun make_bad_spec(): Outer {
    make_bad_outer()
}
