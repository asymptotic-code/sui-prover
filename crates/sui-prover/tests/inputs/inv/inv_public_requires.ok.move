module 0x42::inv_public_requires;

public struct S has copy, drop {
    x: u64
}

#[spec_only]
public fun S_inv(s: &S): bool {
    s.x > 0
}

public fun use_s(s: S): u64 {
    s.x
}

#[spec(prove)]
fun test(): u64 {
    use_s(S { x: 0 })
}
