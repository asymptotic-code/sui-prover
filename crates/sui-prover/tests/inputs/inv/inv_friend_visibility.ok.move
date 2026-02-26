module 0x42::inv_friend_visibility;

public struct S has copy, drop {
    x: u64
}

#[spec_only]
public fun S_inv(s: &S): bool {
    s.x > 0
}

public(package) fun make_bad(): S {
    S { x: 0 }
}

// make_bad is public(package) and has ensures(S_inv(result)) from Part A.
// It returns S { x: 0 } which violates x > 0.
#[spec(prove)]
fun make_bad_spec(): S {
    make_bad()
}
