module 0x42::inv_public_ensures;

public struct S has copy, drop {
    x: u64
}

#[spec_only]
public fun S_inv(s: &S): bool {
    s.x > 0
}

public fun make_bad(): S {
    S { x: 0 }
}

public fun make_good(): S {
    S { x: 1 }
}

// This spec calls make_bad which has ensures(S_inv(result)) from Part A.
// make_bad returns S { x: 0 } which violates x > 0, so ensures should fail.
#[spec(prove)]
fun make_bad_spec(): S {
    make_bad()
}
