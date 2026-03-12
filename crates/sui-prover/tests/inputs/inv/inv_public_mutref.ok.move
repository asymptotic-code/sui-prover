module 0x42::inv_public_mutref;

public struct S has copy, drop {
    x: u64
}

#[spec_only]
public fun S_inv(s: &S): bool {
    s.x > 0
}

public fun set_zero(s: &mut S) {
    s.x = 0;
}

public fun set_one(s: &mut S) {
    s.x = 1;
}

// set_zero has ensures(S_inv(s)) from Part A, which fails because s.x = 0
#[spec(prove)]
fun test_bad(s: &mut S) {
    set_zero(s)
}
