module 0x42::inv_private_no_check;

public struct S has copy, drop {
    x: u64
}

#[spec_only]
public fun S_inv(s: &S): bool {
    s.x > 0
}

fun make_bad(): S {
    S { x: 0 }
}

public fun wrap(): S {
    let mut s = make_bad();
    s.x = 1;
    s
}

#[spec(prove)]
fun wrap_spec(): S {
    wrap()
}
