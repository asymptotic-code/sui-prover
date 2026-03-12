module 0x42::helper {
    public fun identity_val(x: u64): u64 {
        x
    }
}

module 0x42::inv_cross_module_assert {
    public struct S has copy, drop {
        x: u64
    }

    #[spec_only]
    public fun S_inv(s: &S): bool {
        s.x > 0
    }

    // This public function calls a cross-module function.
    // Part B wraps the cross-module call with assert-before on S-typed args.
    // Since s.x is a u64 (not S), the cross-module assert doesn't directly apply here,
    // but the public function still has requires/ensures from Part A.
    public fun process(s: &S): u64 {
        0x42::helper::identity_val(s.x)
    }

    // process has requires(S_inv(s)) from Part A and returns u64 (no ensures).
    // This spec verifies process. The function is correct.
    #[spec(prove)]
    fun process_spec(s: &S): u64 {
        process(s)
    }
}
